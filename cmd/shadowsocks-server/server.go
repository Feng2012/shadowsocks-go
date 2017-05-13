package main

import (
	"encoding/binary"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"os"
	"os/signal"
	"runtime"
	"strconv"
	"sync"
	"syscall"

	ss "github.com/shadowsocks/shadowsocks-go/shadowsocks"
)

import (
	"encoding/json"
	"html/template"
	"io/ioutil"
	"math/rand"
	"net/http"
	"strings"
	"time"

	"github.com/codegangsta/negroni"
	"github.com/goincremental/negroni-sessions"
	"github.com/goincremental/negroni-sessions/cookiestore"
)

var debug ss.DebugLog

const dnsGoroutineNum = 64

func getRequest(conn *ss.Conn) (host string, extra []byte, err error) {
	const (
		idType  = 0 // address type index
		idIP0   = 1 // ip addres start index
		idDmLen = 1 // domain address length index
		idDm0   = 2 // domain address start index

		typeIPv4 = 1 // type is ipv4 address
		typeDm   = 3 // type is domain address
		typeIPv6 = 4 // type is ipv6 address

		lenIPv4   = 1 + net.IPv4len + 2 // 1addrType + ipv4 + 2port
		lenIPv6   = 1 + net.IPv6len + 2 // 1addrType + ipv6 + 2port
		lenDmBase = 1 + 1 + 2           // 1addrType + 1addrLen + 2port, plus addrLen
	)

	// buf size should at least have the same size with the largest possible
	// request size (when addrType is 3, domain name has at most 256 bytes)
	// 1(addrType) + 1(lenByte) + 256(max length address) + 2(port)
	buf := make([]byte, 260)
	var n int
	// read till we get possible domain length field
	ss.SetReadTimeout(conn)
	if n, err = io.ReadAtLeast(conn, buf, idDmLen+1); err != nil {
		return
	}

	reqLen := -1
	switch buf[idType] {
	case typeIPv4:
		reqLen = lenIPv4
	case typeIPv6:
		reqLen = lenIPv6
	case typeDm:
		reqLen = int(buf[idDmLen]) + lenDmBase
	default:
		err = fmt.Errorf("addr type %d not supported", buf[idType])
		return
	}

	if n < reqLen { // rare case
		ss.SetReadTimeout(conn)
		if _, err = io.ReadFull(conn, buf[n:reqLen]); err != nil {
			return
		}
	} else if n > reqLen {
		// it's possible to read more than just the request head
		extra = buf[reqLen:n]
	}

	// Return string for typeIP is not most efficient, but browsers (Chrome,
	// Safari, Firefox) all seems using typeDm exclusively. So this is not a
	// big problem.
	switch buf[idType] {
	case typeIPv4:
		host = net.IP(buf[idIP0 : idIP0+net.IPv4len]).String()
	case typeIPv6:
		host = net.IP(buf[idIP0 : idIP0+net.IPv6len]).String()
	case typeDm:
		host = string(buf[idDm0 : idDm0+buf[idDmLen]])
	}
	// parse port
	port := binary.BigEndian.Uint16(buf[reqLen-2 : reqLen])
	host = net.JoinHostPort(host, strconv.Itoa(int(port)))
	return
}

const logCntDelta = 100

var connCnt int
var nextLogConnCnt int = logCntDelta

func handleConnection(conn *ss.Conn) {
	var host string

	connCnt++ // this maybe not accurate, but should be enough
	if connCnt-nextLogConnCnt >= 0 {
		// XXX There's no xadd in the atomic package, so it's difficult to log
		// the message only once with low cost. Also note nextLogConnCnt maybe
		// added twice for current peak connection number level.
		log.Printf("Number of client connections reaches %d\n", nextLogConnCnt)
		nextLogConnCnt += logCntDelta
	}

	// function arguments are always evaluated, so surround debug statement
	// with if statement
	if debug {
		debug.Printf("new client %s->%s\n", conn.RemoteAddr().String(), conn.LocalAddr())
	}
	closed := false
	defer func() {
		if debug {
			debug.Printf("closed pipe %s<->%s\n", conn.RemoteAddr(), host)
		}
		connCnt--
		if !closed {
			conn.Close()
		}
	}()

	host, extra, err := getRequest(conn)
	if err != nil {
		log.Println("error getting request", conn.RemoteAddr(), conn.LocalAddr(), err)
		return
	}
	debug.Println("connecting", host)
	remote, err := net.Dial("tcp", host)
	if err != nil {
		if ne, ok := err.(*net.OpError); ok && (ne.Err == syscall.EMFILE || ne.Err == syscall.ENFILE) {
			// log too many open file error
			// EMFILE is process reaches open file limits, ENFILE is system limit
			log.Println("dial error:", err)
		} else {
			log.Println("error connecting to:", host, err)
		}
		return
	}
	defer func() {
		if !closed {
			remote.Close()
		}
	}()
	// write extra bytes read from
	if extra != nil {
		// debug.Println("getRequest read extra data, writing to remote, len", len(extra))
		if _, err = remote.Write(extra); err != nil {
			debug.Println("write request extra error:", err)
			return
		}
	}
	if debug {
		debug.Printf("piping %s<->%s", conn.RemoteAddr(), host)
	}
	go ss.PipeThenClose(conn, remote)
	ss.PipeThenClose(remote, conn)
	closed = true
	return
}

type PortListener struct {
	password string
	listener net.Listener
}

type PasswdManager struct {
	sync.Mutex
	portListener map[string]*PortListener
}

func (pm *PasswdManager) add(port, password string, listener net.Listener) {
	pm.Lock()
	pm.portListener[port] = &PortListener{password, listener}
	pm.Unlock()
}

func (pm *PasswdManager) get(port string) (pl *PortListener, ok bool) {
	pm.Lock()
	pl, ok = pm.portListener[port]
	pm.Unlock()
	return
}

func (pm *PasswdManager) del(port string) {
	pl, ok := pm.get(port)
	if !ok {
		return
	}
	pl.listener.Close()
	pm.Lock()
	delete(pm.portListener, port)
	pm.Unlock()
}

// Update port password would first close a port and restart listening on that
// port. A different approach would be directly change the password used by
// that port, but that requires **sharing** password between the port listener
// and password manager.
func (pm *PasswdManager) updatePortPasswd(port, password string) {
	pl, ok := pm.get(port)
	if !ok {
		log.Printf("new port %s added\n", port)
	} else {
		if pl.password == password {
			return
		}
		log.Printf("closing port %s to update password\n", port)
		pl.listener.Close()
	}
	// run will add the new port listener to passwdManager.
	// So there maybe concurrent access to passwdManager and we need lock to protect it.
	go run(port, password)
}

var passwdManager = PasswdManager{portListener: map[string]*PortListener{}}

func updatePasswd() {
	log.Println("updating password")
	newconfig, err := ss.ParseConfig(configFile)
	if err != nil {
		log.Printf("error parsing config file %s to update password: %v\n", configFile, err)
		return
	}
	oldconfig := config
	config = newconfig

	if err = unifyPortPassword(config); err != nil {
		return
	}
	for port, passwd := range config.PortPassword {
		passwdManager.updatePortPasswd(port, passwd)
		if oldconfig.PortPassword != nil {
			delete(oldconfig.PortPassword, port)
		}
	}
	// port password still left in the old config should be closed
	for port, _ := range oldconfig.PortPassword {
		log.Printf("closing port %s as it's deleted\n", port)
		passwdManager.del(port)
	}
	log.Println("password updated")
}

func waitSignal() {
	var sigChan = make(chan os.Signal, 1)
	signal.Notify(sigChan, syscall.SIGHUP)
	for sig := range sigChan {
		if sig == syscall.SIGHUP {
			updatePasswd()
		} else {
			// is this going to happen?
			log.Printf("caught signal %v, exit", sig)
			os.Exit(0)
		}
	}
}

func run(port, password string) {

	var addr string
	var lastTime int64

	ln, err := net.Listen("tcp", ":"+port)
	if err != nil {
		log.Printf("error listening port %v: %v\n", port, err)
		return
	}
	passwdManager.add(port, password, ln)
	var cipher *ss.Cipher
	log.Printf("server listening port %v ...\n", port)
	for {
		conn, err := ln.Accept()
		if err != nil {
			// listener maybe closed to update password
			debug.Printf("accept error: %v\n", err)
			return
		}

		hostPort := strings.Split(conn.RemoteAddr().String(), ":")
		nowtime := time.Now().Unix()
		if hostPort[0] != addr && nowtime <= lastTime+10 {
			conn.Close()
			continue
		}
		lastTime = nowtime
		addr = hostPort[0]

		// Creating cipher upon first connection.
		if cipher == nil {
			log.Println("creating cipher for port:", port)
			cipher, err = ss.NewCipher(config.Method, password)
			if err != nil {
				log.Printf("Error generating cipher for port: %s %v\n", port, err)
				conn.Close()
				continue
			}
		}
		go handleConnection(ss.NewConn(conn, cipher.Copy()))
	}
}

func enoughOptions(config *ss.Config) bool {
	return config.ServerPort != 0 && config.Password != ""
}

func unifyPortPassword(config *ss.Config) (err error) {
	if len(config.PortPassword) == 0 { // this handles both nil PortPassword and empty one
		if !enoughOptions(config) {
			fmt.Fprintln(os.Stderr, "must specify both port and password")
			return errors.New("not enough options")
		}
		port := strconv.Itoa(config.ServerPort)
		config.PortPassword = map[string]string{port: config.Password}
	} else {
		if config.Password != "" || config.ServerPort != 0 {
			fmt.Fprintln(os.Stderr, "given port_password, ignore server_port and password option")
		}
	}
	return
}

var configFile string
var config *ss.Config

func main() {
	log.SetFlags(log.Ldate | log.Ltime | log.Lshortfile)
	log.SetOutput(os.Stdout)

	var cmdConfig ss.Config
	var printVer bool
	var core int
	var webPort int

	flag.BoolVar(&printVer, "version", false, "print version")
	flag.StringVar(&configFile, "c", "config.json", "specify config file")
	flag.StringVar(&cmdConfig.Password, "k", "", "password")
	flag.IntVar(&cmdConfig.ServerPort, "p", 0, "server port")
	flag.IntVar(&cmdConfig.Timeout, "t", 60, "connection timeout (in seconds)")
	flag.StringVar(&cmdConfig.Method, "m", "", "encryption method, default: aes-256-cfb")
	flag.IntVar(&core, "core", 0, "maximum number of CPU cores to use, default is determinied by Go runtime")
	flag.BoolVar((*bool)(&debug), "d", false, "print debug message")
	flag.IntVar(&webPort, "web", 3000, "web port")

	flag.Parse()

	if printVer {
		ss.PrintVersion()
		os.Exit(0)
	}

	ss.SetDebug(debug)

	var err error
	config, err = ss.ParseConfig(configFile)
	if err != nil {
		if !os.IsNotExist(err) {
			fmt.Fprintf(os.Stderr, "error reading %s: %v\n", configFile, err)
			os.Exit(1)
		}
		config = &cmdConfig
	} else {
		ss.UpdateConfig(config, &cmdConfig)
	}
	if config.Method == "" {
		config.Method = "aes-256-cfb"
	}
	if err = ss.CheckCipherMethod(config.Method); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err = unifyPortPassword(config); err != nil {
		os.Exit(1)
	}
	if core > 0 {
		runtime.GOMAXPROCS(core)
	}

	rand.Seed(time.Now().UnixNano())
	if runtime.GOOS == "linux" {
		limitConfig.Init("/etc/limit.json")
	} else {
		limitConfig.Init("limit.json")
	}

	for port, password := range config.PortPassword {
		go run(port, password)
	}

	go runWeb(webPort)
	go DaysLimitLoop()

	waitSignal()
}

type PortConfig struct {
	EndDate  string
	Password string
	Port     int
}

type LimitConfig struct {
	sync.RWMutex
	Password  string                 `json:"password"`
	Secret    string                 `json:"secret"`
	PortLimit map[string]*PortConfig `json:"port_limit"`

	filename string
}

var limitConfig = &LimitConfig{
	PortLimit: make(map[string]*PortConfig),
	filename:  "limit.json",
}

func saveStruct(st interface{}, path string) (err error) {
	b, err := json.MarshalIndent(st, "", "  ")
	if err == nil {
		err = ioutil.WriteFile(path, b, 0644)
	}
	checkErr(err)
	return
}

func getFreePort() int {
	addr, err := net.ResolveTCPAddr("tcp", "localhost:0")
	if err != nil {
		return 0
	}

	l, err := net.ListenTCP("tcp", addr)
	if err != nil {
		return 0
	}
	defer l.Close()
	return l.Addr().(*net.TCPAddr).Port
}

func freePort(port int) {
	passwdManager.del(strconv.Itoa(port))
}

func (c *LimitConfig) Init(file string) {

	c.Lock()
	c.filename = file
	b, err := ioutil.ReadFile(file)
	if err == nil {
		json.Unmarshal(b, c)
		if c.PortLimit == nil {
			c.PortLimit = make(map[string]*PortConfig)
		}
	}
	c.Unlock()

	c.RLock()
	for port, conf := range c.PortLimit {
		go run(port, conf.Password)
	}
	c.RUnlock()
}

func checkErr(err error) {
	if err != nil {
		log.Println(err)
	}
}

func (c *LimitConfig) Save() error {
	return saveStruct(c, c.filename)
}

func (c *LimitConfig) Del(portStr string, save, lock bool) error {

	var err error

	if lock {
		c.Lock()
	}
	if _, ok := c.PortLimit[portStr]; ok {
		delete(c.PortLimit, portStr)
		if save == true {
			err = c.Save()
		}
	} else {
		err = errors.New("port not exist")
	}
	if lock {
		c.Unlock()
	}

	if err == nil {
		var port int
		port, err = strconv.Atoi(portStr)
		freePort(port)
	}
	return err
}

func (c *LimitConfig) Add(days int) (*PortConfig, error) {

	if days <= 0 {
		return nil, errors.New("不可使用0天")
	}

	password := RandSeq(8)
	port := getFreePort()
	if port == 0 {
		return nil, errors.New("getPort error: no spare ports")
	}

	y, m, d := time.Unix(time.Now().Unix()+int64(days+1)*24*3600, 0).Date()
	dateStr := fmt.Sprintf("%d-%d-%d", y, m, d)
	pcon := &PortConfig{EndDate: dateStr, Password: password, Port: port}

	c.Lock()
	c.PortLimit[strconv.Itoa(port)] = pcon
	err := c.Save()
	c.Unlock()

	if err == nil {
		go run(strconv.Itoa(port), password)
		return pcon, nil
	}
	return nil, err
}

func runWeb(port int) {

	mux := http.NewServeMux()
	mux.HandleFunc("/config", handleConfig)
	mux.HandleFunc("/", handleLogin)

	n := negroni.Classic()
	if limitConfig.Secret == "" {
		limitConfig.Lock()
		limitConfig.Secret = RandSeq(4)
		limitConfig.Save()
		limitConfig.Unlock()
	}
	store := cookiestore.New([]byte(limitConfig.Secret))
	n.Use(sessions.Sessions("ss", store))
	//n.Use(gzip.Gzip(gzip.DefaultCompression))
	n.UseHandler(mux)
	n.Run(":" + strconv.Itoa(port))
}

var loginTml = template.Must(template.New("login").Parse(`
<!DOCTYPE html>
<html lang="zh-cn">

<head>
    <meta charset="utf-8">
    <meta http-equiv="X-UA-Compatible" content="IE=edge">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>登陆</title>
</head>
<body style="background-color: rgb(221,221,221);">
    <form method="get" style="margin-top:100px;text-align:center;">
        <input type="text" name="pwd" placeholder="密码" />
        <input type="submit" value="{{.btn_val}}" />
		{{if .pwd_empty}}<br/>请输入密码 {{end}} 
		{{if .pwd_err}}<br/>密码错误 {{end}}
    </form>
</body>
</html>
`))

func renderLogin(w http.ResponseWriter, param map[string]interface{}) {
	err := loginTml.Execute(w, param)
	checkErr(err)
}

func handleNoConfigurePwd(w http.ResponseWriter, req *http.Request) {
	req.ParseForm()
	var loginParam = make(map[string]interface{})
	pwd := req.FormValue("pwd")
	if pwd != "" {
		limitConfig.Lock()
		limitConfig.Password = pwd
		limitConfig.Save()
		limitConfig.Unlock()

		session := sessions.GetSession(req)
		session.Set("pwd", pwd)

		http.Redirect(w, req, "/config", http.StatusFound)
		return
	}
	loginParam["btn_val"] = "设置密码"
	renderLogin(w, loginParam)
	return
}

func handleNoSession(session sessions.Session, w http.ResponseWriter, req *http.Request, confPwd string) {
	req.ParseForm()
	var loginParam = make(map[string]interface{})
	pwd := req.FormValue("pwd")
	if pwd != confPwd {
		loginParam["btn_val"] = "登录"
		if pwd != "" {
			loginParam["pwd_err"] = true
		}
		renderLogin(w, loginParam)
		return
	}
	session.Set("pwd", pwd)
	http.Redirect(w, req, "/config", http.StatusFound)
	return
}

func handleLogin(w http.ResponseWriter, req *http.Request) {

	if req.URL.Path != "/" {
		http.NotFound(w, req)
		return
	}

	limitConfig.RLock()
	confPwd := limitConfig.Password
	limitConfig.RUnlock()

	if confPwd == "" {
		handleNoConfigurePwd(w, req)
		return
	}

	session := sessions.GetSession(req)
	sessPwd := session.Get("pwd")
	if sessPwd == nil {
		handleNoSession(session, w, req, confPwd)
		return
	}

	sessPwdStr, ok := sessPwd.(string)
	if ok && sessPwdStr == confPwd {
		http.Redirect(w, req, "/config", http.StatusFound)
		return
	}
	handleNoSession(session, w, req, confPwd)
}

var configTml = template.Must(template.New("config").Parse(`
<!DOCTYPE html>
<html lang="zh-cn">

<head>
    <meta charset="utf-8">
    <meta http-equiv="X-UA-Compatible" content="IE=edge">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>config</title>
</head>

<body style="background-color: rgb(221,221,221); ">
    <div style="text-align:center;margin:10px;margin-top:100px;">
        <form method="post"><input type="text" name="days" placeholder="使用天数" />
            <input type="submit" value="增加" />
        </form>
        {{if .add_suc}}{{with .add_suc}}端口：{{.Port}}<br/>密码：{{.Password}}<br/>可使用到：
		{{.EndDate}}之前{{end}}{{end}} {{.add_err}}
    </div>
    <div style="text-align:center;margin:10px;">
        <form method="post">
            <input type="text" name="port" placeholder="端口号" />
            <input type="submit" value="删除" />
        </form>{{.del_suc}}{{.del_err}}
    </div>
	<table style="text-align:center;margin-left: auto;margin-right: auto;">
	<tr><th>端口</th><th>密码</th><th>结束日期</th></tr>
	{{range $key, $value := .all_ports}}
	<tr><td>{{$value.Port}}</td><td>{{$value.Password}}</td><td>{{$value.EndDate}}</td></tr>
	{{end}}
	</table>
</body>

</html>
`))

func renderConfig(w http.ResponseWriter, param map[string]interface{}) {
	err := configTml.Execute(w, param)
	checkErr(err)
}

func loginOk(w http.ResponseWriter, req *http.Request) bool {
	limitConfig.RLock()
	confPwd := limitConfig.Password
	limitConfig.RUnlock()
	session := sessions.GetSession(req)
	sessPwd := session.Get("pwd")
	sessPwdStr, ok := sessPwd.(string)
	if !(ok && sessPwdStr == confPwd) {
		http.Redirect(w, req, "/", http.StatusFound)
		return false
	}
	return true
}

func initAllPort(param map[string]interface{}) {
	var config = make(map[string]*PortConfig)
	limitConfig.RLock()
	for port, conf := range limitConfig.PortLimit {
		config[port] = conf
	}
	limitConfig.RUnlock()
	param["all_ports"] = config
}

func handleConfig(w http.ResponseWriter, req *http.Request) {

	if loginOk(w, req) == false {
		return
	}

	param := make(map[string]interface{})
	if req.Method == "GET" {
		initAllPort(param)
		renderConfig(w, param)
		return
	}

	req.ParseForm()

	daystr := req.FormValue("days")
	if daystr != "" {
		days, _ := strconv.Atoi(daystr)
		pcon, err := limitConfig.Add(days)
		if err == nil {
			param["add_suc"] = pcon
		} else {
			param["add_err"] = err
		}
	} else {
		param["add_err"] = "请输入使用多少天"
	}

	portStr := req.FormValue("port")
	if portStr != "" {
		err := limitConfig.Del(portStr, true, true)
		if err == nil {
			param["del_suc"] = "删除成功"
		} else {
			param["del_err"] = err
		}
	} else {
		param["del_err"] = "请输入要删除的端口"
	}

	initAllPort(param)

	renderConfig(w, param)

}

var letters = []byte("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890")

func RandSeq(n int) string {
	b := make([]byte, n)
	for i := range b {
		b[i] = letters[rand.Int()%len(letters)]
	}
	return string(b)
}

func DaysLimitLoop() {

	_, _, nowday := time.Now().Date()
	for {

		nowtime := time.Now()
		_, _, daynew := nowtime.Date()
		if daynew != nowday {
			nowday = daynew

			limitConfig.Lock()
			for k, v := range limitConfig.PortLimit {
				if v.EndDate != "" {
					var y, m, d int
					fmt.Sscanf(v.EndDate, "%d-%d-%d", &y, &m, &d)
					endDateTime := time.Date(y, time.Month(m), d, 0, 0, 0, 0, nil)

					if nowtime.Unix() > endDateTime.Unix() {
						checkErr(limitConfig.Del(k, false, false))
					}

				}
			}
			limitConfig.Save()
			limitConfig.Unlock()
		}
		time.Sleep(20 * time.Minute)
	}

}
