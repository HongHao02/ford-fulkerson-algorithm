///#MENU                  ///FIND BY
///              ---CLASS---
/// queue class:            #queue
/// vertex class:           #ver
/// residualEdge class:     #e01
/// edge class:             #e02
/// graph class:            #g

///             ---GENERAL FUNCTIONS---
///Lay toa do vertex:       #getCoords
///Save graph               #save
///Restore graph            #restore
///Drag                     #drag
///Zoom graph               #MouseWheelHandler
///Mouse Pressed            #mousePressed 
///Create Vertex            #mouseDbClick  
///Mouse moving             #mouseMove
///Mouse Released           #mouseReleased
///Show vertexMenu          #showVertex
///Show edgeMenu            #showEdge
///Get Position             #getPosition

///             ---MENU CLICK---
///Moving vertex            #moveVertex
///Removing vertex          #removeVertex
///Removing edge            #removeEdge
///flip                     #flip
///Change Edge capacity     #setCapcity
///Cancel                   #cancel
///Hide Vertex Menu         #hideVertexMenu
///Hide Edge Menu           #hideEdgeMenu
///Choose Source            #chooseS
///Choose Sink              #chooseSink
///Disable button menu      #disableButtonMenu

///             ---SIMPLE GRAPH---
///Random graph             #randomGraph
///Random Edge              #randomEdge
/// GraphSaple:             #simpleGraph

///             ---ALGORITHM---
///check neighbor           #isNeighbors
///check flow vs capacity   #flowLessThanCapacity
///min(a,b)                 #min
///fordfullkerson fullStep  #fordfullkerson

///playALgorithm            #playNoAnimation
///find path between S&T    #findPath
///fill table of conten     #fillTable
///blink ver                #myBlinkVertexPromise
///blink edge               #blinkEdge
///blink asyn               #excuteAnimaionBlinkAsync
///reset annimation         #resetAnimationAffect
///Clear table content      #clearTableContent
///SLIDER range             #sliderFunction
///PAUSE/RESUME             #PAUSE/RESUME

///////////end menu///

/*My code define */
const infi = 999;

let tb6ver = document.getElementById("tb6ver");
let tb8ver = document.getElementById("tb8ver");




/**************************** main **************************************/
var radius = 20; // vertex radius.
var container = document.getElementById("contentContainer"); // container for both canvas.
var canvas = document.getElementById('canvas'); // flow network canvas.
var canvas2 = document.getElementById('canvas2'); // residual network canvas.
var context = canvas.getContext("2d"); // flow network context.
var context2 = canvas2.getContext("2d"); // residual network context.
var vertexMenu = document.getElementById("vertexMenu"); // vertex menu.
vertexMenu.style.display = 'none';
var edgeMenu = document.getElementById("edgeMenu"); // edge menu.
edgeMenu.style.display = 'none';
var mygraph = new graph(); // flow network database and functions.
var copyGraph, copyS, copyT;
var maxCapacity = 100; // edges maximum capacity.

document.getElementById("maxCap").onchange = function () { // sets new max capacity.
    var cap = parseInt(document.getElementById("maxCap").value);
    if (cap < 10)
        cap = 10;
    maxCapacity = cap;
}



///mycode

canvas.ondblclick = mouseDblClick; // mouse double click handler

///

/* mouse attributes */
canvas.onmousedown = mousePressed; // mouse pressed handler.
canvas.onmouseup = mouseReleased; // mouse released handler.
canvas.onmousemove = drag; // mouse move handler.
canvas.addEventListener("mousewheel", MouseWheelHandler, false); // mouse wheel handler.
canvas2.addEventListener("mousewheel", MouseWheelHandler, false); // mouse wheel handler.
var hitVertex = -1; // clicked vertex id.
var hitEdge = -1; // clicked edge id.
var coords = {
    x: 0,
    y: 0
}; // mouse location cords.

// let divCanvas = document.getElementById("div-container-canvas");
// let divCanvas2 = document.getElementById("div-container-canvas2");
// canvas.width=divCanvas.offsetWidth;
// canvas.height=divCanvas.offsetHeight;
// canvas2.width=divCanvas2.offsetWidth;
// canvas2.height=divCanvas2.offsetHeight;

// window.addEventListener('resize', function() {
//     canvas.width = divCanvas.offsetWidth;
//     canvas.height = divCanvas.offsetHeight;
// });


var dragging = false;
var idleMouseUp = false;
var showingVertexMenu = false;
var showingEdgeMenu = false;
var draggingVertex = false;

/* canvas properties */
var offset = 10; // offset to draw edge from center.
var fontSize = 12;
context2.font = fontSize + "pt Times New Roman";
context.font = fontSize + "pt Times New Roman";

/* algorithm attributes */
// var alg = 0; //0-edmonds karp, 1-capacity scaling.
// document.getElementById("algorithm").onchange = function () { // sets algorithm type.
//     if (document.getElementById("algorithm").value === "edmondsKarp")
//         alg = 0;
//     else alg = 1;
//     mygraph.clearAlg();
// }
var playing = false;

var delta; // for capacity scaling algorithm.
var Cf; // how much can we augment?
var maxFlow; // the max flow.
var p; // the augmenting path.
var source = -1; // source id.
var sink = -1; // sink id.
document.getElementById('restoreB').disabled = true;
var playB = document.getElementById('playButton');
var clrAlg = document.getElementById('clearAlg');
clrAlg.disabled = true;

/* animation */
var blink = null;
var interval;
var speed = 50;

/* Queue Class (FIFO) - used in BFS() and with blinking animation */
///#queue
function Queue() {
    this.arr = [];

    /*make the queue become null */
    this.makeNullQueue = function () {
        this.arr.splice(0, this.arr.length);
    }
    /* return true if Queue is empty, else return false */
    this.isEmpty = function () {
        if (this.arr.length === 0)
            return true;
        else return false;
    };

    /* add new element to head */
    this.enqueue = function (item) {
        this.arr.unshift(item);
    };

    /* remove and return the last element on the Queue */
    this.dequeue = function () {
        if (this.isEmpty === true)
            return null;
        else return this.arr.pop();
    };

    /* return last element in the queue */
    this.getHead = function () {
        if (this.isEmpty === true)
            return null;
        else return this.arr[this.arr.length - 1];
    };

    /* remove and return first element */
    this.popHead = function () {
        if (this.isEmpty === true)
            return null;
        else return this.arr.shift();
    };
} // Queue Class


///#ver

function Vertex(id, x, y, color) {
    /* Vertex Class */
    /// <summary>create a new Vertex</summary>  
    /// <param name='id' type="Number">special id</param> 
    /// <param name='x' type="Number">x coordinate</param>  
    /// <param name='y' type="Number">y coordinate</param>  
    /// <param name='color' type="String">color to draw</param>  

    this.id = id;
    this.x = x;
    this.y = y;
    if (color === null)
        this.color = "white";
    else this.color = color;

    //attributes for algorithms
    this.neighbors = []; // adjacency list for the residual network.
    this.prev = -1; // previous vertex.
    this.flag = 0; // indicates wheter a node is treated or not. (color white,red,black).
    this.dist = -1; // distance from S.


    ///MY_CODE
    this.sigma = infi; ///define sigma of vertex

    this.dir = 0; ///define direction of vertex ( 0 , 1: + , -1: -)



    ///END

    this.setPosition = function (x, y) {
        /// <summary>sets Vertex's new position</summary>  
        /// <param name='x' type="Number">x coordinate</param>  
        /// <param name='y' type="Number">y coordinate</param>  
        this.x = x;
        this.y = y;
        this.draw();
    };


    /* draws a Vertex */
    this.draw = function () {
        context.beginPath();
        context2.beginPath();
        if (this.id == source || this.id == sink) {
            context.arc(this.x, this.y, radius + 5, 0, 2 * Math.PI, false);
            context2.arc(this.x, this.y, radius + 5, 0, 2 * Math.PI, false);
        } else {
            context.arc(this.x, this.y, radius, 0, 2 * Math.PI, false);
            context2.arc(this.x, this.y, radius, 0, 2 * Math.PI, false);
        }

        context.fillStyle = this.color;
        context2.fillStyle = this.color;
        context.fill();
        context2.fill();
        context.lineWidth = 1;
        context2.lineWidth = 1;
        context.strokeStyle = '#003300';
        context2.strokeStyle = '#003300';
        context.stroke();
        context2.stroke();
        context.closePath();
        context2.closePath();
        if (this.color === "white" || this.color === "yellow") {
            context.fillStyle = 'black';
            context2.fillStyle = 'black';
        } else {
            context.fillStyle = 'white';
            context2.fillStyle = 'white';
        }
        context.save();
        context2.save();
        context.textBaseline = 'middle';
        context2.textBaseline = 'middle';
        context.textAlign = 'center';
        context2.textAlign = 'center';
        if (this.id == source) {
            context.fillText("Source" + this.id, this.x, this.y);
            context2.fillText("Source" + this.id, this.x, this.y);
        } else if (this.id == sink) {
            context.fillText("Sink" + this.id, this.x, this.y);
            context2.fillText("Sink" + this.id, this.x, this.y);
        } else {
            context.fillText(this.id, this.x, this.y);
            context2.fillText(this.id, this.x, this.y);
        }

        context.restore();
        context2.restore();
    };

    /* copy a vertex without algorithm properties */
    this.copy = function () {
        return new Vertex(this.id, this.x, this.y, this.color);
    };


    ///MYCODE
    this.getPrev = function () {
        return this.prev;
    }
} // Vertex Class


///#e01
function ResidualEdge(u, v, c) {
    /// <summary>create a new Residual Edge (u,v)</summary>  
    /// <param name='u' type="Number">Vertex u id</param> 
    /// <param name='v' type="Number">Vertex v id</param>  
    /// <param name='c' type="Number">Edge capacity</param>  

    this.u = u; // from Vertex id
    this.v = v; // to Vertex id
    this.c = c; // capacity
    this.color = "darkgreen";
    this.reverseEdge = null;
    this.flag = false;

    /* Draw the residual edge in the residual network */
    this.draw = function () {
        var from = getCoords(u);
        var to = getCoords(v);

        // as vector from p1 to p2
        var nx = to.x - from.x;
        var ny = to.y - from.y;

        // get length
        const len = Math.sqrt(nx * nx + ny * ny);
        // use the length to normalise the vector
        nx /= len;
        ny /= len;

        context2.setTransform(
            nx, ny, // the x axis
            -ny, nx, // the y axis at 90 deg to the x axis
            from.x, from.y // the origin (0,0)
        )

        context.lineWidth = 2;
        context2.lineWidth = 2;
        context2.fillStyle = this.color;
        context2.strokeStyle = this.color;
        if (this.reverseEdge.c === 0 || this.c === 0) {
            var c = this.c;
            if (this.c === 0) {
                c = this.reverseEdge.c;
                context2.fillStyle = 'brown';
                context2.strokeStyle = 'brown';
            }

            context2.beginPath();
            context2.lineTo(0, 0); // start of line
            context2.lineTo(len, 0); // end of line
            context2.stroke();

            // add the arrow head
            if (this.c === 0) {
                context2.beginPath();
                context2.lineTo(radius, 0); // tip of arrow
                context2.lineTo(radius + 10, 5);
                context2.lineTo(radius + 10, -5);
                context2.fill();
            } else {
                context2.beginPath();
                context2.lineTo(len - radius, 0); // tip of arrow
                context2.lineTo(len - 10 - radius, 5);
                context2.lineTo(len - 10 - radius, -5);
                context2.fill();
            }

            context2.save();
            context2.textBaseline = 'bottom';
            context2.textAlign = 'center';
            if (this.flag === false)
                context2.fillText(c, len / 2, -2);
            else
                context2.fillText("+" + Cf, len / 2, -2);
            context2.restore();
        } else {
            context2.beginPath();
            context2.lineTo(0, offset); // start of line
            context2.lineTo(len, offset); // end of line
            context2.stroke();
            var tip = Math.sqrt(radius * radius - offset * offset);
            // add the arrow head
            context2.beginPath();
            context2.lineTo(len - tip, offset); // tip of arrow
            context2.lineTo(len - 10 - radius, offset + 5);
            context2.lineTo(len - 10 - radius, offset - 5);
            context2.fill();

            context2.beginPath();
            context2.fillStyle = 'brown';
            context2.strokeStyle = 'brown';
            context2.moveTo(0, -offset); // start of second line
            context2.lineTo(len, -offset); // end of second line
            context2.stroke();

            // add second  arrow head
            context2.beginPath();
            context2.lineTo(tip, -offset); // tip of arrow
            context2.lineTo(10 + radius, -offset + 5);
            context2.lineTo(10 + radius, -offset - 5);
            context2.fill();

            // text
            context2.save();
            context2.textBaseline = 'bottom';
            context2.fillStyle = 'darkgreen';
            context2.textAlign = 'center';
            if (this.flag === false)
                context2.fillText(this.c, len / 2, offset + 20);
            else context2.fillText("+" + Cf, len / 2, offset + 20);
            context2.fillStyle = 'brown';
            context2.fillText(this.reverseEdge.c, len / 2, -offset - 2);
            context2.restore();
        }
        context2.setTransform(1, 0, 0, 1, 0, 0); // restore default transform
    }; // draw

} // ResidualEdge

///#e02

function Edge(u, v, c) {
    /* Edge Class */
    /// <summary>create a new Edge (u,v)</summary>  
    /// <param name='u' type="Number">Vertex u id</param> 
    /// <param name='v' type="Number">Vertex v id</param>  
    /// <param name='c' type="Number">Edge capacity</param>  

    this.u = u; // from Vertex id
    this.v = v; // to Vertex id
    this.c = c; // capacity
    this.f = 0; // flow
    this.color = "black";
    this.residualEdge = -1; // residual edge index.
    this.flag = false; // indicates what to draw/show flow when increase path
    this.showfflag = false; //show sigma
    this.sigmaEdge = 0; //indicates sigma of vertex on head edge
    this.verDir = true; ///Cho biet cung nay la cung thuan hay cung nghich

    /* Draws edge */
    this.draw = function () {
        mygraph.residual[this.residualEdge].draw(); // draw Edge in residual network.

        var from = getCoords(this.u);
        var to = getCoords(this.v);

        // as vector from p1 to p2
        var dx = to.x - from.x;
        var dy = to.y - from.y;

        // get length
        const len = Math.sqrt(dx * dx + dy * dy);
        // use the length to normalise the vector
        dx /= len;
        dy /= len;

        context.setTransform(
            dx, dy, // the x axis
            -dy, dx, // the y axis at 90 deg to the x axis
            from.x, from.y // the origin (0,0)
        )

        context.fillStyle = this.color;
        context.strokeStyle = this.color;
        context.lineWidth = 2;
        context2.lineWidth = 2;
        context.beginPath();
        context.lineTo(0, 0); // start of line
        context.lineTo(len, 0); // end of line
        context.stroke();

        // add the arrow head
        context.beginPath();
        context.lineTo(len - radius, 0); // tip of arrow
        context.lineTo(len - 10 - radius, 5);
        context.lineTo(len - 10 - radius, -5);
        context.fill();

        /* draw text */
        context.save();
        context.textBaseline = 'bottom';
        context.textAlign = 'center';
        var txt;

        if (this.showfflag) {
            context.fillStyle = 'green';
            txt = "~~~> " + this.sigmaEdge;
        } else {
            if (this.flag === false) {
                context.fillStyle = 'blue';
                txt = this.c;
                if (this.f > 0) {
                    txt = this.f + " / " + txt;
                }
            } else {
                context.fillStyle = 'red';
                txt = "+" + Cf;
            }
        }




        context.fillText(txt, len / 2, -2);
        context.restore();
        context.setTransform(1, 0, 0, 1, 0, 0); // restore default transform
    }; // draw()

    /* copy an edge without algorithm peoperties */
    this.copy = function () {
        return new Edge(this.u, this.v, this.c);
    };
} // Edge Class

///#g
/* Graph data structure and fucntions */
function graph() {
    this.vertices = [];
    this.edges = [];
    this.n = 0; // vertices count (for id)
    this.residual = []; // representing edges in the residual network

    /* if graph contains no vertices, return true. else, return false. */
    this.isEmpty = function () {
        if (this.vertices.length === 0)
            return true;
        return false;
    };

    this.addVertex = function (x, y, color) {
        /// <summary>add a new Vertex</summary>  
        /// <param name='x' type="Number">x coordinate</param> 
        /// <param name='y' type="Number">y coordinate</param> 
        /// <param name='color' type="String">Vertex draw color</param> 

        this.n++;
        this.vertices.push(new Vertex(this.n, x, y, color));
        this.clearAlg();
    };

    this.addEdge = function (u, v, c) {
        /// <summary>add a new Edge (u,v) </summary>  
        /// <param name='u' type="Number">Vertex u id</param> 
        /// <param name='v' type="Number">Vertex v id</param> 
        /// <param name='c' type="Number">Edge capacity</param> 

        if (u === v || c === 0) return;
        if (this.existsEdge(u, v) || this.existsEdge(v, u)) return; // if edge exist, do nothing.
        var edge = new Edge(u, v, c);

        /* update residual network */
        var residualEdge = new ResidualEdge(u, v, c);
        var reverseEdge = new ResidualEdge(v, u, 0);
        residualEdge.reverseEdge = reverseEdge;
        reverseEdge.reverseEdge = residualEdge;
        this.residual.push(residualEdge);
        edge.residualEdge = this.residual.length - 1;

        this.edges.push(edge);

        /* register neighbors (residual network) */
        this.vertices[this.getIndex(u)].neighbors.push(this.vertices[this.getIndex(v)]);
        this.clearAlg();
    };

    this.existsEdge = function (u, v) {
        /// <summary>check if edge exist</summary>  
        /// <param name='u' type="Number">Vertex u id</param> 
        /// <param name='v' type="Number">Vertex v id</param> 
        /// <returns type="Boolean">true if Edge exist</returns>
        for (var i = 0; i < this.edges.length; i++) {
            if ((u === this.edges[i].u && v === this.edges[i].v)) {
                return true;
            }
        }
        return false;
    };

    this.inEdge = function (x, y) {
        /// <summary>check if clicked on an Edge</summary>  
        /// <param name='x' type="Number">x click coordinate</param> 
        /// <param name='y' type="Number">y click coordinate</param> 
        /// <returns type="Number">Edge index or -1 if not found</returns>

        var x1, y1, x2, y2;
        var i1, i2;
        for (var i = 0; i < this.edges.length; i++) {
            i1 = this.getIndex((this.edges[i]).u);
            i2 = this.getIndex((this.edges[i]).v);
            x1 = this.vertices[i1].x;
            y1 = this.vertices[i1].y;
            x2 = this.vertices[i2].x;
            y2 = this.vertices[i2].y;

            //test if the point (x,y) is near the line
            var distance = Math.abs((y - y2) * x1 - (x - x2) * y1 + x * y2 - y * x2) / Math.sqrt(Math.pow((y - y2), 2) + Math.pow((x - x2), 2));
            if (distance > 10) continue;
            //test if the point (x,y) is between edge (u,v)
            var dotproduct = (x - x1) * (x2 - x1) + (y - y1) * (y2 - y1)
            if (dotproduct < 0) continue;
            var squaredlengthba = (x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1);
            if (dotproduct <= squaredlengthba) return i;
        }
        return -1;
    };

    this.deleteVertex = function (id) {
        /// <summary>Delete a Vertex</summary>  
        /// <param name='id' type="Number">Vertex id</param> 

        var i = this.getIndex(id);
        if (i !== -1) // if vertex exist, remove it.
            this.vertices.splice(i, 1);

        for (i = this.edges.length - 1; i >= 0; i--) { // remove all edges associated with the vertex.
            if (this.edges[i].u === id || this.edges[i].v === id)
                this.edges.splice(i, 1);
        }

        /* remove from neighbors lists */
        var j, n;
        for (i = 0; i < this.vertices.length; i++) {
            n = this.vertices[i].neighbors;
            for (j = n.length - 1; j >= 0; j--)
                if (id === n[j].id) {
                    n.splice(j, 1);
                    continue;
                }
        }
        this.clearAlg();
    };

    this.deleteEdge = function (index) {
        /// <summary>Delete an Edge</summary>  
        /// <param name='index' type="Number">Edge's index</param> 

        if (index !== -1) { // if edge exist
            /* remove from residual edges */
            this.residual.splice(this.edges[index].residualEdge, 1);
            /*update indexe*/
            var i = this.edges[index].residualEdge;
            for (; i < this.edges.length; i++)
                this.edges[i].residualEdge--;


            /* remove from neighbors lists */
            var v = this.edges[index].v;
            i = this.getIndex(this.edges[index].u);
            for (j = 0; j < this.vertices[i].neighbors.length; j++) {
                if (v === this.vertices[i].neighbors[j].id) {
                    this.vertices[i].neighbors.splice(j, 1);
                    break;
                }
            }
            this.edges.splice(index, 1);
            this.clearAlg();
        }
    };


    this.inVertex = function (x, y) {
        /// <summary>check if clicked on Vertex</summary>  
        /// <param name='x' type="Number">x click coordinate</param> 
        /// <param name='y' type="Number">y click coordinate</param> 
        /// <returns type="Number">Vertex id or -1 if not found</returns>

        let d = radius;
        let i;
        for (i = 0; i < this.vertices.length; i++) {
            console.log(Math.abs(x - this.vertices[i].x) + "__d " + Math.abs(y - this.vertices[i].y))
            if (Math.abs(x - this.vertices[i].x) <= d && Math.abs(y - this.vertices[i].y) <= d) {
                console.log("x,y is in vertex")
                return this.vertices[i].id;
            }
        }
        return -1;
    };



    /* Delete all Vertices and Edges */
    this.reset = function () {
        /* reset configuration */
        clearInterval(interval);
        playing = false;
        maxFlow = 0;
        Cf = 0;
        document.getElementById("MaxFlowText").value = maxFlow;
        document.getElementById("aug").value = 0;
        document.getElementById("path").value = 0;

        ///Remove the animation "algani"
        bkt.classList.remove("algani");
        bdo.classList.remove("algani");
        bkt1.classList.remove("algani");
        blq.classList.remove("algani");
        bhx.classList.remove("algani");
        bct.classList.remove("algani");
        bcn.classList.remove("algani");
        bdt.classList.remove("algani");
        bwh.classList.remove("algani");
        btl.classList.remove("algani");
        btlct.classList.remove("algani");
        btlcn.classList.remove("algani");



        ///Remove all script
        script.innerHTML = "";
        step_script.innerHTML = "";

        clearTableContent(); ///ClearTable Data
        sink = -1;
        source = -1;
        var i;
        for (i = this.vertices.length; i > 0; i--) { // reset vertices.
            this.vertices.pop();
        }
        this.n = 0;
        for (i = this.edges.length; i > 0; i--) { // reset edges.
            this.edges.pop();
        }
        for (i = this.residual.length; i > 0; i--) { // reset residual edges.
            this.residual.pop();
        }
        // playB.disabled = false;
        document.getElementById('saveB').disabled = false;
        clrAlg.disabled = true;
        this.clearCanvas();
        this.draw();
    };

    /* clear algorithm data, the graph stays the same */
    this.clearAlg = function () {
        clearInterval(interval);
        maxFlow = 0;

        //mycode

        sumFlow = 0;
        countFlow = 0;

        blinkVer = new Queue();
        blinkEdge = new Queue();

        clearTableContent();
        document.getElementById("MaxFlowText").value = sumFlow;
        document.getElementById("path").value = countFlow;
        document.getElementById("aug").value = 0;

        ///Remove the animation "algani"
        bkt.classList.remove("algani");
        bdo.classList.remove("algani");
        bkt1.classList.remove("algani");
        blq.classList.remove("algani");
        bhx.classList.remove("algani");
        bct.classList.remove("algani");
        bcn.classList.remove("algani");
        bdt.classList.remove("algani");
        bwh.classList.remove("algani");
        btl.classList.remove("algani");
        btlct.classList.remove("algani");
        btlcn.classList.remove("algani");


        //To mau cac Ver and Edge ve lai mau cua no
        for (let ver of this.vertices) {
            ver.color = 'white';
            if (ver.id == source) {
                ver.color = "green";
            }
            if (ver.id == sink) {
                ver.color = "yellow";
            }
        }

        ///Remove all script
        script.innerHTML = "";
        step_script.innerHTML = "";

        //
        Cf = 0;
        delta = 0;
        // document.getElementById("MaxFlowText").value = maxFlow;
        // document.getElementById("aug").value = 0;
        // document.getElementById("path").value = 0;
        playing = false;
        var edge, n, j, flag, i;
        for (i = 0; i < this.edges.length; i++) {
            edge = this.edges[i];
            edge.f = 0;
            edge.flag = false;
            edge.color = 'black';
            this.residual[edge.residualEdge].flag = false;
            this.residual[edge.residualEdge].color = 'darkgreen';
            this.residual[edge.residualEdge].c = edge.c;
            this.residual[edge.residualEdge].reverseEdge.c = 0;

            // re-register neighbors (residual network) 
            if (edge.c > 0) {
                n = this.vertices[this.getIndex(edge.u)].neighbors;
                flag = false;
                for (j = 0; j < n.length; j++) {
                    if (n[j].id === edge.v)
                        flag = true;
                }
                if (flag === false)
                    n.push(this.vertices[this.getIndex(edge.v)]);
            }
        }

        // ClearAlg
        for (i = 0; i < this.edges.length; i++) {
            this.edges[i].f =0;
            this.edges[i].flag =false;
            this.edges[i].showfflag=false;
            console.log("remove flag and showfflag")
           
        }
        
        for (i = 0; i < this.vertices.length; i++) {
            this.vertices[i].prev = -1;
            this.vertices[i].flag = 0;
            this.vertices[i].dist = -1;
        }


        if (p !== null && p !== undefined)
            p.splice(0, p.length);
        else p = [];

        // playB.disabled = false;
        document.getElementById('saveB').disabled = false;
        clrAlg.disabled = true;
        this.clearCanvas();
        this.draw();


    };

    /* Draw the graph */
    this.draw = function () {
        var i;
        for (i = 0; i < this.edges.length; i++) {
            this.edges[i].draw();
        }
        for (i = 0; i < this.vertices.length; i++) {
            this.vertices[i].draw();
        }
    };

    /* resets the canvas */
    this.clearCanvas = function () {
        context.clearRect(0, 0, canvas.width, canvas.height);
        context2.clearRect(0, 0, canvas2.width, canvas2.height);
    };



    this.getIndex = function (id) {
        /// <summary>get Vertex index in vertices array</summary>  
        /// <param name='id' type="Number">Vertex id number</param> 
        /// <returns type="Number">Vertex id or -1 if not found</returns>
        for (var i = 0; i < this.vertices.length; i++) {
            if (this.vertices[i].id === id) {
                return i;
            }
        }
        return -1;
    };

    this.getEdge = function (u, v) {
        /// <summary>get Edge index</summary>  
        /// <param name='u' type="Number">Vertex id number</param> 
        /// <param name='v' type="Number">Vertex id number</param> 
        /// <returns type="Number">Edge Index or -1 if not found</returns>
        var i;
        for (i = 0; i < this.edges.length; i++) {
            if (this.edges[i].u === u && this.edges[i].v === v)
                return i;
        }
        return -1;
    };


    this.getCapcity = function (u, v) {
        /// <summary>get Edge capacity</summary>  
        /// <param name='u' type="Number">Vertex object</param> 
        /// <param name='v' type="Number">Vertex object</param> 
        /// <returns type="Number">Edge Capacity or -1 if not found</returns>

        let edge = this.getEdge(u.id, v.id);
        if (edge !== -1) {
            return this.edges[edge].c
        }
        return -1;
    }

    this.getFlow = function (u, v) {
        /// <summary>get Edge Flow</summary>  
        /// <param name='u' type="Number">Vertex object</param> 
        /// <param name='v' type="Number">Vertex object</param> 
        /// <returns type="Number">Edge Flow or -1 if not found</returns>
        let edge = this.getEdge(u.id, v.id);
        if (edge !== -1) {
            return this.edges[edge].f
        }
        return -1;
    }

    this.insideVertex = function (positionX, positionY) {
        for (let i = 0; i < this.vertices.length; i++) {
            let distance = Math.sqrt(Math.pow(this.vertices[i].x - positionX, 2) + Math.pow(this.vertices[i].y - positionY, 2));
            if (distance <= 20) {
                return i;
            }
        }
        return -1;
    }

    ///MY_CODE

    ///END

    this.updateResidual = function (f, c, index) {
        /// <summary>update residual network</summary>  
        /// <param name='f' type="Number">Flow</param> 
        /// <param name='c' type="Number">Capacity</param> 
        /// <param name='index' type="Number">Edge index</param> 

        if (c === f) { // remove from neighbors
            var n = this.vertices[this.getIndex(this.edges[index].u)].neighbors;
            var i;
            for (i = 0; i < n.length; i++) {
                if (n[i].id === this.edges[index].v) {
                    n.splice(i, 1);
                    break;
                }
            }
        }
        var edge = this.edges[index].residualEdge;
        if (edge !== -1) {
            this.residual[edge].c = c - f;
            this.residual[edge].reverseEdge.c = f;
        }
        this.clearCanvas();
        this.draw();
    };

    /* copy the entire graph without algorithm properties */
    this.copy = function () {
        var newGraph = new graph();
        var i, residualEdge, reverseEdge, e;
        /* copy vertices */
        for (i = 0; i < this.vertices.length; i++)
            newGraph.vertices.push(this.vertices[i].copy());
        newGraph.n = this.n;

        /* copy edges and residual edges */
        for (i = 0; i < this.edges.length; i++) {
            e = this.edges[i].copy();
            residualEdge = new ResidualEdge(e.u, e.v, e.c);
            reverseEdge = new ResidualEdge(e.v, e.u, 0);
            residualEdge.reverseEdge = reverseEdge;
            reverseEdge.reverseEdge = residualEdge;
            newGraph.residual.push(residualEdge);
            e.residualEdge = newGraph.residual.length - 1;
            newGraph.edges.push(e);
        }

        /* register neighbors */
        newGraph.clearAlg();
        return newGraph;
    };
} // Graph class


/*************************** general functions *************************************/

///#getCoords
function getCoords(id) {
    /// <summary>get Vertex coordinates</summary>  
    /// <param name='id' type="Number">Vertex id number</param> 
    /// <returns>Vertex coordinates or null if not found</returns>
    var i = mygraph.getIndex(id);
    if (i != -1) {
        return {
            x: mygraph.vertices[i].x,
            y: mygraph.vertices[i].y
        };
    } else return null;
};

///#save
/* save the current graph */
function save() {
    copyGraph = mygraph.copy();
    copyS = source;
    copyT = sink;
    document.getElementById('restoreB').disabled = false;
}

///#restore
/* restore last saved graph */
function restore() {
    mygraph.reset();
    mygraph = copyGraph;
    source = copyS;
    sink = copyT;
    mygraph.draw();
    document.getElementById('restoreB').disabled = true;
}

///#drag
/* Vertex Dragging */
function drag(e) {
    // var parentPosition = getPosition(e.currentTarget);
    // var xPosition = e.clientX - parentPosition.x;
    // var yPosition = e.clientY - parentPosition.y;

    let xPosition = e.offsetX;
    let yPosition = e.offsetY;

    if (dragging) {
        context.clearRect(0, 0, canvas.width, canvas.height);
        context.beginPath();
        context.moveTo(coords.x, coords.y);
        context.lineTo(xPosition, yPosition);
        context.stroke();
        mygraph.draw();
        return;
    } else if (draggingVertex) {
        var i = mygraph.getIndex(hitVertex);
        mygraph.vertices[i].setPosition(xPosition, yPosition);
        mygraph.clearCanvas();
        mygraph.draw();
    }
}

///#MouseWheelHandler
/* mouse wheel handler - used for zooming in / out */
function MouseWheelHandler(e) {
    var d = Math.max(-1, Math.min(1, (e.wheelDelta || -e.detail)));
    if (d < 0) {
        radius -= 2;
        if (radius < 15)
            radius = 15;
        offset--;
        if (offset < 5)
            offset = 5;
        fontSize--;
        if (fontSize < 10)
            fontSize = 10;
    } else {
        radius += 2;
        if (radius > 25)
            radius = 25;
        offset++;
        if (offset > 10)
            offset = 15;
        fontSize++;
        if (fontSize > 15)
            fontSize = 15;
    }
    context2.font = fontSize + "pt Times New Roman";
    context.font = fontSize + "pt Times New Roman";
    mygraph.clearCanvas();
    mygraph.draw();
    return false;
}

///#mousePressed
/* mouse pressed handler */
function mousePressed(e) {

    if (showingVertexMenu || showingEdgeMenu) {
        return;
    }
    if (draggingVertex) {
        draggingVertex = false;
        idleMouseUp = true;
        return;
    }
    // let parentPosition = getPosition(e.currentTarget);
    // let xPosition = e.clientX - parentPosition.x;
    // let yPosition = e.clientY - parentPosition.y;

    let rect = canvas.getBoundingClientRect();
    let xP = e.clientX - rect.left;
    let yP = e.clientY - rect.top;



    // console.log("mousePressed " + parentPosition +"_"+ xPosition + "_"+ yPosition);
    console.log("mousePressed (" + xP + "," + yP + ")");


    // hitVertex = mygraph.inVertex(xPosition, yPosition);
    hitVertex = mygraph.inVertex(xP, yP);
    console.log("hitVertex " + hitVertex)
    if (hitVertex !== -1) { // clicked on vertex
        coords = getCoords(hitVertex);
        dragging = true;
        return;
    }
    hitEdge = mygraph.inEdge(xP, yP);
    if (hitEdge !== -1) {
        mygraph.edges[hitEdge].color = "red";
        mygraph.clearCanvas();
        mygraph.draw();
        return;
    }
    idleMouseUp = true;
    // mygraph.addVertex(xPosition, yPosition, "white");
    mygraph.clearCanvas();
    mygraph.draw();
}

let isMove = false;
let parentColor = "white";
///#mouseDbClick
/* mouse double click handler */
function mouseDblClick(e) {
    isMove = false;
    if (showingVertexMenu || showingEdgeMenu) {
        return;
    }

    if (draggingVertex) {
        draggingVertex = false;
        idleMouseUp = true;
        return;
    }

    // let parentPosition = getPosition(e.currentTarget);
    // let xPosition = e.clientX - parentPosition.x;
    // let yPosition = e.clientY - parentPosition.y;

    // let xPosition = e.offsetX - 20;
    // let yPosition = e.offsetY - 20;

    // Vị trí bị sai
    // let rect= canvas.getBoundingClientRect();
    // let xPosition= e.clientX - rect.left;
    // let yPosition= e.clientX - rect.top;

    let xPosition = e.offsetX;
    let yPosition = e.offsetY;


    mygraph.addVertex(xPosition, yPosition, "white");
    // mygraph.addVertex(x, y, "white");
    mygraph.clearCanvas();
    mygraph.draw();
}

let overVer;
// canvas.addEventListener("mousemove", e => {
//     isMove = true;

//     // if (isMove) {
//     //     if (context.isPointInPath(e.offsetX, e.offsetY)) {
//     //         overVer = mygraph.inVertex(e.offsetX, e.offsetY);
//     //         parentColor = mygraph.vertices[mygraph.getIndex(overVer)].color;
//     //         mygraph.vertices[mygraph.getIndex(overVer)].color = "red";
//     //         mygraph.clearCanvas();
//     //         mygraph.draw();
//     //     }

//     //     if (!context.isPointInPath(e.offsetX, e.offsetY) || mygraph.inVertex(e.offsetX, e.offsetY) !== overVer) {
//     //         mygraph.vertices[mygraph.getIndex(overVer)].color = parentColor;
//     //         mygraph.clearCanvas();
//     //         mygraph.draw();
//     //     }
//     // }

//     if(isMove){
//         if (mygraph.insideVertex(e.offsetX + 20, e.offsetY + 20)!=-1) {
//             // overVer = mygraph.inVertex(e.offsetX, e.offsetY);
//             overVer = mygraph.insideVertex(e.offsetX, e.offsetY);
//             parentColor = mygraph.vertices[overVer].color;
//             mygraph.vertices[overVer].color = "red";
//             mygraph.clearCanvas();
//             mygraph.draw();
//         }  
//     }

//     isMove=false;


// })

///#mouseMove
canvas.addEventListener("mousemove", function (e) {

})

// canvas.addEventListener("mousedown",(event) => {

//     dragging = false;
//     if (showingVertexMenu || showingEdgeMenu) {
//         hideEdgeMenu();
//         hideVertexMenu();
//         hitEdge = -1;
//         hitVertex = -1;
//         return;
//     }
//     if (idleMouseUp) {
//         idleMouseUp = false;
//         hitEdge = -1;
//         hitVertex = -1;
//         return;
//     }
//     // let parentPosition = getPosition(e.currentTarget);
//     // let xPosition = e.clientX - parentPosition.x;
//     // let yPosition = e.clientY - parentPosition.y;

//     let xPosition =e.offsetX;
//     let yPosition =e.offsetY;
//     console.log(xPosition,yPosition);
//     let hit = mygraph.inVertex(xPosition, yPosition);
//     if (hit > -1) {
//         if (hit === hitVertex) {
//             showVertexMenu(xPosition, yPosition);
//         } 
//     } else {
//         if (hitEdge !== -1) {
//             showEdgeMenu(xPosition, yPosition);
//         }
//         mygraph.clearCanvas();
//         mygraph.draw();
//     }

// })


///#mouseReleased
/* mouse released handler */
function mouseReleased(e) {
    dragging = false;
    if (showingVertexMenu || showingEdgeMenu) {
        hideEdgeMenu();
        hideVertexMenu();
        hitEdge = -1;
        hitVertex = -1;
        return;
    }
    if (idleMouseUp) {
        idleMouseUp = false;
        hitEdge = -1;
        hitVertex = -1;
        return;
    }
    // let parentPosition = getPosition(e.currentTarget);
    // let xPosition = e.clientX - parentPosition.x;
    // let yPosition = e.clientY - parentPosition.y;

    let xPosition = e.offsetX;
    let yPosition = e.offsetY;

    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    console.log("Position of pointer: "+ x+","+y)

    //Vị trí bị sai
    // let rect= canvas.getBoundingClientRect();
    // let xPosition= e.clientX - rect.left;
    // let yPosition= e.clientX - rect.top;

    console.log(xPosition, yPosition);
    let hit = mygraph.inVertex(xPosition, yPosition);
    console.log(hit)
    if (hit > -1) {
        if (hit !== hitVertex) {
            let c = Number(prompt("Enter Capacity:", ""));
            if (c <= 0)
                alert("Invalid capacity!");
            else {
                mygraph.addEdge(hitVertex, hit, c);
            }
            mygraph.clearCanvas();
            mygraph.draw();
        } else {
            // showVertexMenu(xPosition, yPosition);
            // showVertexMenu(xClient, yClient);
            showVertexMenu(x,y);
        }
    } else {
        if (hitEdge !== -1) {
            // showEdgeMenu(xPosition, yPosition);
            // showEdgeMenu(xClient, yClient);
            showEdgeMenu(x,y);
        }
        mygraph.clearCanvas();
        mygraph.draw();
    }
}

///#showVertex
/* Show Vertex Menu in position (x,y) */
function showVertexMenu(x, y) {
    showingVertexMenu = true;
    if (playing === true)
        disableCriticalButtons();
    else enableCriticalButtons();
    // vertexMenu.style.left = x + Math.round(vertexMenu.offsetWidth) + 'px';
    vertexMenu.style.left = (x + 141 )+ 'px'
    // vertexMenu.style.top = y + Math.round(vertexMenu.offsetHeight) + 'px';
    vertexMenu.style.top = (y+477) + 'px';

    // canvas.parentNode.appendChild(vertexMenu);
    vertexMenu.style.display = 'block';
}

///#showEdge
/* Show Edge Menu in position (x,y) */
function showEdgeMenu(x, y) {
    showingEdgeMenu = true;
    let e = mygraph.edges[hitEdge];
    if (playing === true)
        disableCriticalButtons();
    else enableCriticalButtons();
    if (e.u === source || e.u === sink || e.v === source || e.v === sink)
        document.getElementById("eButton1").disabled = true;
    else document.getElementById("eButton1").disabled = false;
    edgeMenu.style.display = 'block';
    edgeMenu.style.left = x + 144 + 'px';
    edgeMenu.style.top = y + 477+ 'px';
}

///#getPosition
/* get position (x,y) of element */
function getPosition(element) {
    let xPosition = 0;
    let yPosition = 0;

    while (element) {
        xPosition += (element.offsetLeft - element.scrollLeft + element.clientLeft);
        yPosition += (element.offsetTop - element.scrollTop + element.clientTop);
        element = element.offsetParent;
    }
    return {
        x: xPosition,
        y: yPosition
    };
}


///                                                                                 ----Menu when click vertex or edge----

///#moveVertex
/* indicate Vertex is dragged */
function moveVertex() {
    draggingVertex = true;
    hideVertexMenu();
}

///#removeVertex
/* Delete a Vertex */
function removeVertex() {
    hideVertexMenu();
    mygraph.deleteVertex(hitVertex);
}

///#removeEdge
/* Delete an Edge */
function removeEdge() {
    hideEdgeMenu();
    mygraph.deleteEdge(hitEdge);
}

///#flip
/* flip edge direction */
function flip() {
    hideEdgeMenu();
    let e = mygraph.edges[hitEdge].copy();
    mygraph.deleteEdge(hitEdge);
    mygraph.addEdge(e.v, e.u, e.c);
}

///#setCapcity
/* change Edge capacity */
function setCapacity() {
    let f = mygraph.edges[hitEdge].f;
    let c = Number(prompt("Enter new Capacity:", ""));
    if (c <= 0) {
        alert("Invalid capacity.");
    } else {
        mygraph.edges[hitEdge].c = c;
    }
    mygraph.updateResidual(f, c, hitEdge);
    hideEdgeMenu();
    mygraph.clearAlg();
}


///#cancel
/* cancel menu */
function cancel() {
    hideVertexMenu();
    hideEdgeMenu();
}

///#hideVertexMenu
/* hide Vertex menu */
function hideVertexMenu() {
    vertexMenu.style.display = 'none';
    showingVertexMenu = false;
}

///#hideEdgeMenu
/* hide Edge menu */
function hideEdgeMenu() {
    edgeMenu.style.display = 'none';
    showingEdgeMenu = false;
    if (hitEdge !== -1)
        mygraph.edges[hitEdge].color = "black";
    mygraph.clearCanvas();
    mygraph.draw();
    document.getElementById("eButton1").disabled = false;
}

///#chooseS
/* mark vertex as source */
function chooseS() {
    hideVertexMenu();
    if (source !== -1)
        mygraph.vertices[mygraph.getIndex(source)].color = "white";
    source = hitVertex;
    mygraph.vertices[mygraph.getIndex(source)].color = "teal";
    mygraph.clearAlg();
    let i;
    for (i = mygraph.edges.length - 1; i >= 0; i--) { // flip relevant edges.
        if (mygraph.edges[i].v === source) {
            hitEdge = i;
            flip();
        }
    }
}

///#ChooseSink
/* mark vertex as sink */
function chooseT() {
    hideVertexMenu();
    if (sink !== -1)
        mygraph.vertices[mygraph.getIndex(sink)].color = "white";
    sink = hitVertex;
    mygraph.vertices[mygraph.getIndex(sink)].color = "yellow";
    mygraph.clearAlg();
    let i;
    for (i = mygraph.edges.length - 1; i >= 0; i--) { // flip relevant edges.
        if (mygraph.edges[i].u === sink) {
            hitEdge = i;
            flip();
        }
    }
}

///#disableButtonMenu
/*disable algorithm - changing buttons */
function disableCriticalButtons() {
    document.getElementById("vButton2").disabled = true;
    document.getElementById("vButton3").disabled = true;
    document.getElementById("vButton4").disabled = true;
    document.getElementById("eButton1").disabled = true;
    document.getElementById("eButton2").disabled = true;
    document.getElementById("eButton3").disabled = true;
}

/*enable algorithm - changing buttons */
function enableCriticalButtons() {
    document.getElementById("vButton2").disabled = false;
    document.getElementById("vButton3").disabled = false;
    document.getElementById("vButton4").disabled = false;
    document.getElementById("eButton1").disabled = false;
    document.getElementById("eButton2").disabled = false;
    document.getElementById("eButton3").disabled = false;
}

/*HighLight button*/
let Vbt1 = document.getElementById("vButton1");
Vbt1.addEventListener('click', function () {
    // Thêm lớp animate__headShake
    Vbt1.classList.add('animate__headShake');

    // Sau 1 giây, xóa lớp animate__headShake
    setTimeout(function () {
        Vbt1.classList.remove('animate__headShake');
    }, 1000);
});





/**************** Sample Graphs ********************/

///#randomGraph
/* Generate a random flow network */
function randomGraph() {
    mygraph.reset();
    /// var graphs = [graph1Sample, graph2Sample, graph3Sample, graph4Sample, graph5Sample, graph6Sample,graph7Sample];  // array of build-graph functions
    var graphs = [ graph6Sample, graph7Sample,graph8Sample]; /// da check minumumCut
    // var graphs = [graph1Sample, graph4Sample, graph4plusSample, graph5Sample, graph6Sample, graph7Sample,graph8Sample];

    // var graphs = [graph6Sample, graph7Sample];
    var i = (Math.floor(Math.random() * 10)) % graphs.length;
    graphs[i]();
    mygraph.draw();
}

///#randomEdge
/* generate a random capacity edge */
function randomEdge(i, j) {
    let c = Math.round((Math.random() * maxCapacity)) % maxCapacity;
    if (i === source || i === sink || j === source || j === sink)
        mygraph.addEdge(i, j, c);
    else {
        let k = Math.random();
        if (k > 0.5)
            mygraph.addEdge(i, j, c);
        else mygraph.addEdge(j, i, c);
    }
}

///#simpleGraph
///graphSample

function graph1Sample() { // simple flow network
    mygraph.addVertex(50, 200, 'teal');
    mygraph.addVertex(150, 100, 'white');
    mygraph.addVertex(150, 300, 'white');
    mygraph.addVertex(300, 100, 'white');
    mygraph.addVertex(300, 300, 'white');
    mygraph.addVertex(380, 200, 'yellow');
    source = 1;
    sink = 6;
    randomEdge(1, 2);
    randomEdge(1, 3);
    randomEdge(2, 4);
    randomEdge(3, 2);
    randomEdge(3, 5);
    randomEdge(4, 3);
    randomEdge(4, 6);
    randomEdge(5, 4);
    randomEdge(5, 6);
}

function graph2Sample() { // complicated flow network
    mygraph.addVertex(50, 200, 'teal');
    mygraph.addVertex(180, 50, 'white');
    mygraph.addVertex(180, 200, 'white');
    mygraph.addVertex(180, 350, 'white');
    mygraph.addVertex(320, 50, 'white');
    mygraph.addVertex(320, 200, 'white');
    mygraph.addVertex(320, 350, 'white');
    mygraph.addVertex(400, 50, 'white');
    mygraph.addVertex(400, 200, 'white');
    mygraph.addVertex(400, 350, 'white');
    mygraph.addVertex(380, 200, 'darkgrey');
    source = 1;
    sink = 11;
    randomEdge(1, 2);
    randomEdge(1, 3);
    randomEdge(1, 4);
    randomEdge(2, 5);
    randomEdge(2, 6);
    randomEdge(2, 7);
    randomEdge(3, 2);
    randomEdge(3, 7);
    randomEdge(3, 8);
    randomEdge(4, 3);
    randomEdge(5, 8);
    randomEdge(5, 10);
    randomEdge(6, 7);
    randomEdge(6, 8);
    randomEdge(7, 4);
    randomEdge(7, 9);
    randomEdge(7, 10);
    randomEdge(8, 11);
    randomEdge(9, 8);
    randomEdge(9, 10);
    randomEdge(9, 11);
    randomEdge(10, 11);
}

function graph3Sample() { // very simple flow network
    mygraph.addVertex(80, 200, 'teal');
    mygraph.addVertex(300, 80, 'white');
    mygraph.addVertex(200, 300, 'white');
    mygraph.addVertex(380, 230, 'darkgrey');
    source = 1;
    sink = 4;
    randomEdge(1, 2);
    randomEdge(1, 4);
    randomEdge(1, 3);
    randomEdge(2, 4);
    randomEdge(3, 2);
    randomEdge(3, 4);
}

function graph4Sample() { // complicated flow network 2
    mygraph.addVertex(25, 200, 'teal'); //ver 1
    mygraph.addVertex(100, 50, 'white'); //2
    mygraph.addVertex(100, 340, 'white'); //3
    mygraph.addVertex(170, 200, 'white'); //4
    mygraph.addVertex(300, 200, 'white'); //5
    mygraph.addVertex(350, 50, 'white'); //6
    mygraph.addVertex(350, 340, 'white'); //7
    mygraph.addVertex(380, 200, 'yellow'); //ver 8
    source = 1;
    sink = 8;
    mygraph.addEdge(1, 2, 10);
    mygraph.addEdge(1, 3, 20);
    mygraph.addEdge(1, 4, 5);
    mygraph.addEdge(2, 4, 7);
    mygraph.addEdge(2, 6, 9);
    mygraph.addEdge(3, 4, 15);
    mygraph.addEdge(3, 7, 18);
    mygraph.addEdge(4, 5, 25);
    mygraph.addEdge(4, 6, 10);
    mygraph.addEdge(4, 7, 6);
    mygraph.addEdge(5, 6, 8);
    mygraph.addEdge(5, 7, 8);
    mygraph.addEdge(5, 8, 6);
    mygraph.addEdge(6, 8, 18);
    mygraph.addEdge(7, 8, 12);
}

function graph4plusSample() { // complicated flow network 2
    mygraph.addVertex(25, 200, 'teal'); //ver 1
    mygraph.addVertex(100, 50, 'white'); //2
    mygraph.addVertex(100, 340, 'white'); //3
    mygraph.addVertex(170, 200, 'white'); //4
    mygraph.addVertex(300, 200, 'white'); //5
    mygraph.addVertex(350, 50, 'white'); //6
    mygraph.addVertex(350, 340, 'white'); //7
    mygraph.addVertex(380, 200, 'yellow'); //ver 8
    source = 1;
    sink = 8;
    randomEdge(1, 2);
    randomEdge(1, 3);
    randomEdge(1, 4);
    randomEdge(2, 4);
    randomEdge(2, 6);
    randomEdge(3, 4);
    randomEdge(3, 7);
    randomEdge(4, 5);
    randomEdge(4, 6);
    randomEdge(4, 7);
    randomEdge(5, 6);
    randomEdge(5, 7);
    randomEdge(5, 8);
    randomEdge(6, 8);
    randomEdge(7, 8);
}

function graph5Sample() { // 3D cube
    mygraph.addVertex(80, 370, 'teal');
    mygraph.addVertex(305, 370, 'white');
    mygraph.addVertex(80, 145, 'white');
    mygraph.addVertex(380, 270, 'white');
    mygraph.addVertex(205, 270, 'white');
    mygraph.addVertex(380, 45, 'white');
    mygraph.addVertex(200, 45, 'white');
    mygraph.addVertex(300, 145, 'yellow');
    source = 1;
    sink = 8;
    randomEdge(1, 2);
    randomEdge(1, 3);
    randomEdge(1, 5);
    randomEdge(2, 4);
    randomEdge(2, 8);
    randomEdge(3, 7);
    randomEdge(3, 8);
    randomEdge(4, 5);
    randomEdge(4, 6);
    randomEdge(5, 7);
    randomEdge(6, 7);
    randomEdge(6, 8);
}

//CHECK
function graph6Sample() { // magen david
    mygraph.addVertex(50, 200, 'teal');
    mygraph.addVertex(100, 50, 'white');
    mygraph.addVertex(300, 50, 'white');
    mygraph.addVertex(100, 350, 'white');
    mygraph.addVertex(300, 350, 'white');
    mygraph.addVertex(380, 200, 'yellow');
    source = 1;
    sink = 6;
    mygraph.addEdge(1, 2, 10);
    mygraph.addEdge(1, 4, 6);
    mygraph.addEdge(2, 3, 7);
    mygraph.addEdge(2, 5, 4);
    mygraph.addEdge(4, 5, 7);
    mygraph.addEdge(2, 5, 4);
    mygraph.addEdge(3, 6, 6);
    mygraph.addEdge(5, 6, 9);


}
//CHECK
function graph7Sample() { // complicated flow network 2
    mygraph.addVertex(25, 200, 'teal'); //ver 1
    mygraph.addVertex(100, 50, 'white'); //2
    mygraph.addVertex(100, 340, 'white'); //3
    mygraph.addVertex(170, 200, 'white'); //4
    mygraph.addVertex(300, 200, 'white'); //5
    mygraph.addVertex(350, 50, 'white'); //6
    mygraph.addVertex(350, 340, 'white'); //7
    mygraph.addVertex(380, 200, 'yellow'); //ver 8
    source = 1;
    sink = 8;
    mygraph.addEdge(1, 2, 10);
    mygraph.addEdge(1, 3, 20);
    mygraph.addEdge(1, 4, 5);
    mygraph.addEdge(2, 4, 7);
    mygraph.addEdge(2, 6, 9);
    mygraph.addEdge(3, 4, 15);
    mygraph.addEdge(3, 7, 18);
    mygraph.addEdge(4, 5, 25);
    mygraph.addEdge(4, 6, 10);
    mygraph.addEdge(4, 7, 6);
    mygraph.addEdge(5, 6, 8);
    mygraph.addEdge(5, 7, 8);
    mygraph.addEdge(5, 8, 6);
    mygraph.addEdge(6, 8, 18);
    mygraph.addEdge(7, 8, 12);
}
//CHECK
function graph8Sample() { // complicated flow network 3
    mygraph.addVertex(50, 120, 'teal'); //ver 1
    mygraph.addVertex(50, 320, 'white'); //2
    mygraph.addVertex(125, 220, 'white'); //3
    mygraph.addVertex(200, 120, 'white'); //4
    mygraph.addVertex(200, 320, 'white'); //5
    mygraph.addVertex(275,220, 'white'); //6
    mygraph.addVertex(350, 120, 'white'); //7
    mygraph.addVertex(350, 320, 'yellow'); //ver 8
    source = 1;
    sink = 8;
    mygraph.addEdge(1, 2, 3);
    mygraph.addEdge(1, 3, 2);
    mygraph.addEdge(1, 4, 3);

    mygraph.addEdge(2, 3, 4);
    mygraph.addEdge(2, 5, 1);

    mygraph.addEdge(3, 4, 1);
    mygraph.addEdge(3, 5, 2);

    mygraph.addEdge(4, 5, 2);
    mygraph.addEdge(4, 7, 6);

    mygraph.addEdge(5, 6, 2);
    mygraph.addEdge(5, 8, 1);

    mygraph.addEdge(6, 4, 4);
    mygraph.addEdge(6, 7, 7);
    mygraph.addEdge(6, 8, 2);

    mygraph.addEdge(7, 8, 9);
    
   
}




///Althogithm

///#isNeighbors
/// x va y co phai la neighbor cua nhau
function isNeighbors(x, v) {
    ///sumary: Cho biet vertex x va v co la neighbor cua nhau
    ///x: vertex object
    ///y: vertex object
    ///return true, if it is not return false
    console.log("IS_NEIGHBOR " + x.id + "_" + v.id)
    let xNeighbors = x.neighbors;
    for (const element of xNeighbors) {
        console.log(element == v)

        if (element == v) {
            return true;
        }
    }
    return false;
}

///#flowLessThanCapacity
///Cho biet luong co nho hon kha nang thong qua khong 
function flowLessThanCapacity(x, v) {
    let exitEdge = mygraph.getEdge(x.id, v.id);
    return !!(exitEdge !== -1 && (mygraph.edges[exitEdge].f < mygraph.edges[exitEdge].c));
}

///#min
///min a and b
function min(a, b) {
    return (a < b) ? a : b;
}


///#fordfullkerson
let sumFlow = 0;

function fordfullkerson(source, sink) {
    let repeatCount = 0; ///Dem so lan lap cua thuat toan fordfullkerson
    let whileCount = 0; ///Dem so lan lap cua while(!Q)
    let Q = new Queue();

    let sourceVertex = mygraph.vertices[mygraph.getIndex(source)]; ///Vertex object
    let sinkVertex = mygraph.vertices[mygraph.getIndex(sink)]; ///Vertex object


    //intit flow
    for (const element of mygraph.edges) {
        element.f = 0;
    }
    console.log("initflow")

    do {
        ///Buoc 1: Xoa nhan cac dinh va gan nhan cho source
        ///       1.1 Xoa tat cac cac nhan
        for (const element of mygraph.vertices) {
            element.dir = 0;
            element.flag = 0;
        }

        ///       1.2 Gan nhan cho dinh source ( +, 1, oo)
        sourceVertex.dir = 1;
        sourceVertex.prev = sourceVertex;
        sourceVertex.sigma = infi;

        // console.log("Gan nhan cho source" + " |dir s: " + sourceVertex.dir + " |prev s: " + sourceVertex.prev + "|sigma s: " + sourceVertex.sigma)

        ///       1.3 Khoi tao QUEUE rong dua source vao QUEUE
        Q.makeNullQueue();
        Q.enqueue(sourceVertex);
        let found = 0; ///Thong bao da gan nhan cho sink chua

        while (!Q.isEmpty()) {
            whileCount++;
            console.log("WHILE LAP LAN " + whileCount);

            console.log(Q)
            ///Lay head ra ==> x
            let x = Q.getHead();
            Q.dequeue();

            for (let v of mygraph.vertices) {

                // alert(v.id);
                ///Xet gan nhan cho cac dinh gan ke voi x (CUNG THUAN)

                console.log(v.dir == 0)
                console.log(isNeighbors(x, v))
                console.log(flowLessThanCapacity(x, v))

                if (v.dir == 0 && isNeighbors(x, v) && flowLessThanCapacity(x, v)) {
                    v.dir = 1;
                    v.prev = x;
                    v.sigma = min(x.sigma, mygraph.getCapcity(x, v) - mygraph.getFlow(x, v));

                    Q.enqueue(v);
                    console.log("CUNG THUAN " + v.id)
                }
                ///Xet gan nhan cho dinh di den x ( XUNG NGHICH)

                console.log(v.dir == 0)
                console.log(mygraph.getCapcity(v, x) > 0)
                console.log(mygraph.getFlow(v, x))

                if (v.dir == 0 && (mygraph.getCapcity(v, x) > 0) && (mygraph.getFlow(v, x) > 0)) {
                    v.dir = -1;
                    v.prev = x;
                    v.sigma = min(x.sigma, mygraph.getFlow(v, x));

                    Q.enqueue(v);
                    console.log("Cung nghich " + v.id)
                }

            }
            ///Neu sink duoc gan nhan tim duoc duong tang luong -> Thoat vong lap
            if (sinkVertex.dir !== 0) {
                found = 1;
                console.log("Tim thay nhan cho sink!" + sinkVertex.dir)

                alert("found in for-----[sink].dir = " + sinkVertex.dir);
                break;
            }
        }


        if (found === 1) {
            repeatCount++;
            alert("TIM THAY DUONG TANG LUONG THU " + repeatCount)

            ///Buoc 4 ,5 6, tang luong
            let x = sinkVertex;
            let sigma = sinkVertex.sigma;
            sumFlow += sigma;


            alert("Tim thay 1 luong cuc dai sigma = " + sigma);
            let blink = new Queue();
            blink.enqueue(x);

            while (x !== sourceVertex) {
                let preV = x.prev;
                blink.enqueue(preV); ///find the previous vertex

                alert("" + preV.id + " is the prev vertex of " + x.id);
                if (x.dir == 1) {
                    mygraph.edges[mygraph.getEdge(preV.id, x.id)].f += sigma;
                }
                if (x.dir == -1) {
                    mygraph.edges[mygraph.getEdge(preV.id, x.id)].f -= sigma;
                }
                x = preV;
            }

            ///In ra cac vertex tren duong tang luong
            // while(!blink.isEmpty()){
            //     let u= blink.getHead();
            //     alert(u.id);
            //     blink.dequeue();
            // }



        } else {
            break; ///Thoat vong lap 
        }
    } while (true);

    alert("SUMFLOW = " + sumFlow);
    document.getElementById("MaxFlowText").value = sumFlow;
}
//                                                              ------------------ALGORITHSM------------------
let possBlink = 0; ///0: nothing to do_find next path; 1: blink Vertex and fill the table; 2: blink Edge
let blinkVer; ///the arr of Vertex object
let blinkEdge; ///the arr of Edge object
let repeatCount = 0; //the number of argumentPath

let blinkEdgeSource; //Queue contain min cut ( source)
let blinkEdgeSink; //Queue contain the order cut

let outofAlgorithm = false;
let finalBlinkVer = new Queue();



let pauseA = document.getElementById("pause");
let resumeA = document.getElementById("resume");

resumeA.disabled = true;
let countFlow = 0; ///count increse flow
let countFlowCopy=0; //copy the countFlow for find the minumum cut


//Blink algorithm

let bkt = document.getElementById("bkt"); ///Khởi tạo f=0
let bdo = document.getElementById("bdo"); ///do
let bkt1 = document.getElementById("bkt1"); ///Xóa nhãn các đỉnh, gán nhãn cho đỉnh 1, Tạo queue mới, đỉnh đầu hàng đợi u
let blq = document.getElementById("blq"); ///Lặp trong khi queue khác rỗng
let bhx = document.getElementById("bhx"); ///Trong tất cả các hàng xóm của u
let bct = document.getElementById("bct"); ///Nếu là cung thuận (đưa vào hàng đợi)
let bcn = document.getElementById("bcn"); ///Nếu là cung nghịch (đưa vào hàng đợi)
let bdt = document.getElementById("bdt"); ///Nếu tìm thấy đỉnh thu (sink) thoát vòng lặp (break)
let bwh = document.getElementById("bwh"); ///while(true)
let btl = document.getElementById("btl"); ///Lấy sigma= sink.sigma Tăng luồng
let btlct = document.getElementById("btlct"); ///Nếu cung thuận +singma
let btlcn = document.getElementById("btlcn"); ///Nếu cung nghịch -singma

///#playNoAnimation
// Play FORDFULLKERSON ALGORITHSM and animation
function playNoAnimation() {




    if (mygraph.vertices.length < 2) {
        alert("Must have at least 2 vertices.");
        return 0;
    }

    if (source === sink || source === -1 || sink === -1) {
        alert("Please choose a source and a sink.");
        return;
    }

    sumFlow = 0; ///reset sumflow
    if (sink != 8) {
        tb6ver.style.display = "block";
        tb8ver.style.display = "none";
    }
    if (sink == 8) {
        tb8ver.style.display = "block";
        tb6ver.style.display = "none";
    }
    //intit flow
    for (const element of mygraph.edges) {
        element.f = 0;
        bkt.classList.add("algani");
        step_script.innerHTML = "Initial f=0";
        bkt.classList.remove("algani");
        bdo.classList.add("algani");
        step_script.innerHTML = "DO";
        // step_script.classList.add("hightLight");
    }



    let possible = findPath(source, sink);
    if (possible) {
        possBlink = 1;
        ////Khoi tao bang du lieu
        excuteAnimationBlinkAsync(); ///play animation

        script.innerHTML += "Iteration 1. Traverse the vertices for the first time. " + "<br>";
        step_script.innerHTML = "Iteration 1. Traverse the vertices for the first time. " + "<br>";
        step_script.style.textAlign = "left";
        step_script.classList.add("hightLight");


    } else {
        alert("There is no argument between source and sink");
    }



    clrAlg.disabled = false;


}

///#findPath
// Tim duong tang luong va tra ve mang cac Vertex da duoc duyet
function findPath(source, sink) {
    let whileCount = 0; ///Dem so lan lap cua while(!Q)
    blinkVer = new Queue();
    blinkEdge = new Queue();

    let Q = new Queue();
    let sourceVertex = mygraph.vertices[mygraph.getIndex(source)]; ///Vertex object
    let sinkVertex = mygraph.vertices[mygraph.getIndex(sink)]; ///Vertex object

    ///Buoc 1: Xoa nhan cac dinh va gan nhan cho source
    ///       1.1 Xoa tat cac cac nhan
    for (const element of mygraph.vertices) {
        bdo.classList.remove("algani");
        bkt1.classList.add("algani");
        element.dir = 0;
        element.flag = 0;
    }

    ///       1.2 Gan nhan cho dinh source ( +, 1, oo)
    sourceVertex.dir = 1;
    sourceVertex.prev = sourceVertex;
    sourceVertex.sigma = infi;

    // console.log("Gan nhan cho source" + " |dir s: " + sourceVertex.dir + " |prev s: " + sourceVertex.prev + "|sigma s: " + sourceVertex.sigma)

    ///       1.3 Khoi tao QUEUE rong dua source vao QUEUE
    Q.makeNullQueue();
    Q.enqueue(sourceVertex);
    blinkVer.enqueue(sourceVertex);
    let found = 0; ///Thong bao da gan nhan cho sink chua

    while (!Q.isEmpty()) {
        whileCount++;
        console.log("WHILE LAP LAN " + whileCount);

        console.log(Q)
        ///Lay head ra ==> x
        let x = Q.getHead();

        Q.dequeue();

        for (let v of mygraph.vertices) {

            // alert(v.id);
            ///Xet gan nhan cho cac dinh gan ke voi x (CUNG THUAN)

            // console.log(v.dir == 0)
            // console.log(isNeighbors(x, v))
            // console.log(flowLessThanCapacity(x, v))

            if (v.dir == 0 && isNeighbors(x, v) && flowLessThanCapacity(x, v)) {
                v.dir = 1;
                v.prev = x;
                v.sigma = min(x.sigma, mygraph.getCapcity(x, v) - mygraph.getFlow(x, v));

                Q.enqueue(v);
                blinkVer.enqueue(v);
                console.log("CUNG THUAN " + v.id)
            }
            ///Xet gan nhan cho dinh di den x ( XUNG NGHICH)

            // console.log(v.dir == 0)
            // console.log(mygraph.getCapcity(v, x) > 0)
            // console.log(mygraph.getFlow(v, x))

            if (v.dir == 0 && (mygraph.getCapcity(v, x) > 0) && (mygraph.getFlow(v, x) > 0)) {
                v.dir = -1;
                v.prev = x;
                v.sigma = min(x.sigma, mygraph.getFlow(v, x));

                Q.enqueue(v);
                blinkVer.enqueue(v);
                console.log("Cung nghich " + v.id)
            }

            ///Neu sink duoc gan nhan tim duoc duong tang luong -> Thoat vong lap
            if (sinkVertex.dir !== 0) {
                found = 1;
                console.log("Tim thay nhan cho sink!" + sinkVertex.dir)
                break;
            }

        }
        
    }

    if (found === 1) {


        countFlow++;
        countFlowCopy=countFlow;
        document.getElementById("path").value = countFlow;
        document.getElementById("aug").value = sinkVertex.sigma;
        repeatCount++;
        // alert("TIM THAY DUONG TANG LUONG THU " + repeatCount)

        ///Buoc 4 ,5 6, tang luong
        let x = sinkVertex;
        let sigma = sinkVertex.sigma;
        sumFlow += sigma;


        // alert("Tim thay 1 luong cuc dai sigma = " + sigma);
        let blink = new Queue();
        blink.enqueue(x);


        while (x !== sourceVertex) {
            let preV = x.prev;

            blink.enqueue(preV); ///find the previous vertex
            blinkEdge.enqueue(mygraph.edges[mygraph.getEdge(preV.id, x.id)]);

            // alert(""+ preV.id + " is the prev vertex of " + x.id);
            if (x.dir == 1) {
                mygraph.edges[mygraph.getEdge(preV.id, x.id)].verDir = true;
            }
            if (x.dir == -1) {
                mygraph.edges[mygraph.getEdge(preV.id, x.id)].verDir = false;
            }
            x = preV;
        }
        console.log("BLINKVER")
        for (let bv of blinkVer.arr) {
            console.log(bv.id);
        }

        return true;

        // console.log(blinkVer)
        // console.log(blinkEdges)


    } else {
        //The spread operator (…), tao array mới, deepcoppy
        finalBlinkVer.arr = [...blinkVer.arr];
        return false;
    }
}

///#fillTable
function fillTable(vertex, flow) {
    /// <summary>Fill table content</summary>  
    /// <param name='vertex' type="Vertex">Vertex object</param> 
    /// <param name='flow' type="Number">Count of increse flow</param> 
    /// <returns >NO</returns>
    let s;
    let dir;
    let sigma;
    let idVer;
    let idLoop;
    let idTable;
    let hd;
    if (sink == 6) {
        s = "";
    } else {
        s = "8_"
    }



    idVer = s + "cl" + vertex.id; ///blink th contain vertex
    idLoop = s + "l" + flow; ///blink row contain vertex
    idTable = s + "rl" + flow + "v" + vertex.id; ///blink cell
    hd = s + "rl" + flow + "hd"; //blink queue
    // console.log("idTable " + idTable);

    document.getElementById(idLoop).classList.add("cl1-affect");
    document.getElementById(idVer).classList.add("cl1-affect");
    document.getElementById(idTable).classList.add("cl1-affect");
    document.getElementById(hd).classList.add("cl1-affect");

    if (vertex.dir == 1) {
        dir = '+';
    } else {
        dir = '-'
    }

    if (vertex.sigma == infi) {
        sigma = "oo"
    } else {
        sigma = vertex.sigma;
    }

    document.getElementById(idTable).innerHTML = "(" + dir + "," + vertex.prev.id + "," + sigma + ")";
    if (vertex.id == 8) {
        document.getElementById(hd).innerHTML += vertex.id;
    } else {
        document.getElementById(hd).innerHTML += vertex.id + ", ";
    }
}

///#myBlinkVertexPromise
function myBlinkVertexPromise() {
    return new Promise((resolve, reject) => {
        let blinkEdgeconnect = -1;
        // let capacityEnable;


        let flag = false; ///dung to mau luan phien tao animation nhap nhay cho vertex va edge

        let ver = blinkVer.getHead();


        blinkVer.dequeue();

        //Blink VERTEX AND FILL THE TABLE
        let count = 0;

        blq.classList.remove("algani");
        bhx.classList.add("algani");

        interval = setInterval(() => {
            if (ver.id != 1) {
                console.log(ver.id);
                if (ver.dir == 1) {
                    blinkEdgeconnect = mygraph.getEdge(ver.prev.id, ver.id);
                } else {
                    blinkEdgeconnect = mygraph.getEdge(ver.id, ver.prev.id);
                }
                // capacityEnable=mygraph.edges[blinkEdgeconnect].c - mygraph.edges[blinkEdgeconnect].f;
                mygraph.edges[blinkEdgeconnect].sigmaEdge = ver.sigma;
            }
            if (count < 10) {
                if (flag) {
                    ver.color = "grey";
                    if (blinkEdgeconnect != -1) {
                        if (ver.dir == 1) {
                            mygraph.edges[blinkEdgeconnect].color = "green";

                        } else {
                            mygraph.edges[blinkEdgeconnect].color = "yellow";
                        }
                    }

                    flag = false;
                } else {
                    ver.color = "red";
                    if (blinkEdgeconnect != -1) {
                        mygraph.edges[blinkEdgeconnect].color = "black";
                    }
                    flag = true;
                }
            }


            if (blinkEdgeconnect !== -1) {
                mygraph.edges[blinkEdgeconnect].showfflag = true;
            }

            mygraph.clearCanvas();
            mygraph.draw();

            let chieu;



            if (ver.dir == 1) {
                chieu = "foward";


                delay(32, speed * 45);
                delay(33, speed * 45);
                delay(34, speed * 45);
                delay(35, speed * 45);
                delay(36, speed * 45);
                delay(37, speed * 45);


                bhx.classList.remove("algani");
                bcn.classList.remove("algani");
                bct.classList.add("algani");


            } else {
                chieu = "backward";
                delay(39, speed * 45);
                delay(40, speed * 45);
                delay(41, speed * 45);
                delay(42, speed * 45);
                delay(43, speed * 45);
                delay(44, speed * 45);
                delay(45, speed * 45);



                bhx.classList.remove("algani");
                bct.classList.remove("algani");
                bcn.classList.add("algani");
            }
            step_script.innerHTML = "TRAVERSAL VERTEX: " + ver.id + " ,DIRECTION: " + chieu + " ,THE PREVIOUS VERTEX: " + ver.prev.id + " ,SIGMA " + ver.sigma + ".<br>";

            step_script.style.textAlign = "left";
            step_script.classList.add("hightLight");



            count++;
            if (!isPause) {
                if (count > 11) {
                    bct.classList.remove("algani");
                    bcn.classList.remove("algani");
                    bhx.classList.add("algani");

                    script.innerHTML += "<span class='text text-danger fst-italic '>TRAVERSAL VERTEX: </span>" + ver.id + " DIRECTION(show the direction): " + ver.dir + " ,pre(The previous vertex) " + ver.prev.id + " ,sigma " + ver.sigma + ".<br>";
                    script.style.textAlign = "left";


                    fillTable(ver, countFlow);
                    count = 0;
                    mygraph.clearCanvas();
                    mygraph.draw();
                    // removeLineClass(34)

                    if (blinkVer.isEmpty()) {

                        delay(47, speed * 45);
                        delay(48, speed * 45);
                        delay(49, speed * 45);
                        delay(50, speed * 45);
                        delay(51, speed * 45);
                        for (let e of mygraph.edges) {
                            e.showfflag = false;
                        }
                        clearInterval(interval);


                        resolve(true);
                    } else {


                        delay(30, speed * 45);
                        ver = blinkVer.getHead();
                        blinkVer.dequeue();
                    }
                }
            }

        }, speed * 10);



    })
}

///#myBlinkVertexPromise
function myBlinkVertexPromise_MinimumCut() {

    return new Promise((resolve, reject) => {
        let blinkEdgeconnect = -1;
        // let capacityEnable;


        let flag = false; ///dung to mau luan phien tao animation nhap nhay cho vertex va edge

        let ver = blinkVer.getHead();


        blinkVer.dequeue();

        //Blink VERTEX AND FILL THE TABLE
        let count = 0;

        interval = setInterval(() => {
            if (ver.id != 1) {
                console.log(ver.id);
                if (ver.dir == 1) {
                    blinkEdgeconnect = mygraph.getEdge(ver.prev.id, ver.id);
                } else {
                    blinkEdgeconnect = mygraph.getEdge(ver.id, ver.prev.id);
                }
                // capacityEnable=mygraph.edges[blinkEdgeconnect].c - mygraph.edges[blinkEdgeconnect].f;
                mygraph.edges[blinkEdgeconnect].sigmaEdge = ver.sigma;
            }
            if (count < 10) {
                if (flag) {
                    ver.color = "grey";
                    if (blinkEdgeconnect != -1) {
                        if (ver.dir == 1) {
                            mygraph.edges[blinkEdgeconnect].color = "green";
                        } else {
                            mygraph.edges[blinkEdgeconnect].color = "yellow";
                        }
                    }

                    flag = false;
                } else {
                    ver.color = "red";
                    if (blinkEdgeconnect != -1) {
                        mygraph.edges[blinkEdgeconnect].color = "black";
                    }
                    flag = true;
                }
            }

            if (blinkEdgeconnect !== -1) {
                mygraph.edges[blinkEdgeconnect].showfflag = true;
            }

            mygraph.clearCanvas();
            mygraph.draw();

            // step_script.innerHTML = "DUYỆT ĐỈNH: " + ver.id + " ,CHIỀU: " + chieu + " ,ĐỈNH CHA: " + ver.prev.id + " ,SIGMA " + ver.sigma + ".<br>";

            step_script.style.textAlign = "left";
            step_script.classList.add("hightLight");

            count++;
            if (!isPause) {
                if (count > 11) {
                    fillTable(ver, countFlowCopy + 1);
                    count = 0;
                    mygraph.clearCanvas();
                    mygraph.draw();

                    if (blinkVer.isEmpty()) {

                        for (let e of mygraph.edges) {
                            e.showfflag = false;
                        }


                        clearInterval(interval);

                        resolve(true);
                    } else {

                        ver = blinkVer.getHead();
                        blinkVer.dequeue();


                    }
                }
            }

        }, speed * 10);



    })
}

///#blinkEdge
function myBlinkEdgePromise() {

    return new Promise((resolve, reject) => {

        bwh.classList.remove("algani");
        btl.classList.add("algani");


        let flag = false; ///Bien to mau luan phien tao animation nhap nhay cho vertex va edge
        Cf = mygraph.vertices[mygraph.getIndex(sink)].sigma;
        delay(52, speed * 45);


        let timeCF = 15;
        while (true) {
            if (timeCF == 0) {
                btl.classList.remove("algani");
                break;
            }
            timeCF--;
        }

        let edge = blinkEdge.popHead();
        delay(54, speed * 45);


        //Blink EDGE AND FILL THE FLOW/CAPACITY
        let count = 0;
        delay(55, speed * 45);
        delay(56, speed * 45);
        delay(57, speed * 45);
        delay(58, speed * 45);

        let time = 40;
        while (time > 0) {
            time--;
        }
        delay(59, speed * 45);


        interval = setInterval(() => {
            if (count > 10) { // blink residual edge
                edge.color = "red";
                if (flag === true) {
                    mygraph.residual[edge.residualEdge].color = "darkgreen";
                    flag = false;
                } else {
                    mygraph.residual[edge.residualEdge].color = "red";
                    flag = true;
                }
                mygraph.residual[edge.residualEdge].flag = true;
            } else {
                if (flag === true) { // blink graph edge
                    edge.color = "black";
                    flag = false;
                } else {
                    edge.color = "red";

                    flag = true;
                }
            }



            //Neu lam theo cach nay thi mau se khong nhap nhay
            // if(count > 10){
            //     edge.color = "red";
            //     mygraph.residual[edge.residualEdge].color = "red";
            // }else{
            //     edge.color = "red";
            // }

            edge.flag = true;
            mygraph.clearCanvas();
            mygraph.draw();




            step_script.innerHTML = "Found the augmenting path for the flow," + countFlow + " Increase edge(" + edge.u + "," + edge.v + ") by " + Cf + "<br>";
            step_script.classList.add("hightLight");
            script.style.textAlign = "left";

            count++;


            bwh.classList.remove("algani");
            btlct.classList.add("algani");
            if (edge.verDir === true) {
                delay(62, speed * 45);
                delay(63, speed * 45);
                delay(64, speed * 45);

            } else {
                delay(65, speed * 45);
                delay(66, speed * 45);
                delay(67, speed * 45);
            }


            if (!isPause) {
                if (count > 20) {
                    btlct.classList.remove("algani");
                    bwh.classList.add("algani");

                    script.innerHTML += "Found an augmenting path for the flow, Increase the  edge's capacity of (" + edge.u + "," + edge.v + ") by " + Cf + "<br>";

                    count = 0;
                    edge.flag = false;
                    mygraph.residual[edge.residualEdge].flag = false;
                    edge.color = "red";
                    if (edge.verDir === true) {
                        edge.f += Cf;

                    } else {
                        edge.f -= Cf;
                    }
                    mygraph.updateResidual(edge.f, edge.c, mygraph.getEdge(edge.u, edge.v));
                    mygraph.clearCanvas();
                    mygraph.draw();
                    if (blinkEdge.isEmpty()) {

                        clearInterval(interval);

                        resolve(true);
                    } else {
                        delay(68, speed * 45);
                        edge = blinkEdge.popHead();

                        let timeDelay2 = 40;
                        while (timeDelay2 > 0) {
                            timeDelay2--;
                        }
                        delay(59, speed * 45);
                    }
                }
            }

        }, speed * 10);



    })
}

///#excuteAnimaionBlinkAsync
const excuteAnimationBlinkAsync = async () => {
    try {

        bkt1.classList.remove("algani");
        blq.classList.add("algani");
        const myStatus = await myBlinkVertexPromise();
        console.log("My myBlinkVertexPromise is successfully " + myStatus);

        //To mau cung chua duong tang luong
        for (let e of blinkEdge.arr) {

            e.color = "orange";
        }

        mygraph.clearCanvas();
        mygraph.draw();

        bhx.classList.remove("algani");
        bct.classList.remove("algani");
        bcn.classList.remove("algani");

        bdt.classList.add("algani");

        let i = 10;
        while (true) {

            if (i == 0) {
                bdt.classList.remove("algani");
                bwh.classList.add("algani");
                break;
            }
            i--;
        }

        const myStatus2 = await myBlinkEdgePromise();
        console.log("My myBlinkEdgePromise is successfully " + myStatus2);

        if (myStatus && myStatus2) {
            delay(11, speed * 45);
            resetAnimationAffect();
        }

    } catch (err) {
        console.log("There are some error: " + err);
    }
}

///#resetAnimationAffect
// Tra cac Edge ve trang thai color binh thuong ( giu nguyen f và c) va findPath tiep tuc
function resetAnimationAffect() {

    //To mau cac Ver and Edge ve lai mau cua no
    for (let ver of mygraph.vertices) {
        ver.color = 'white';
    }
    mygraph.vertices[mygraph.getIndex(source)].color = 'green';
    mygraph.vertices[mygraph.getIndex(sink)].color = 'yellow';

    for (let edge of mygraph.edges) {
        edge.color = 'black';
        edge.verDir = true;
    }

    mygraph.clearCanvas();
    mygraph.draw();

    delayTime(14, speed * 45, 40);
    delayTime(15, speed * 45, 40);
    delayTime(16, speed * 45, 40);
    delayTime(17, speed * 45, 40);

    delayTime(19, speed * 45, 40);
    delayTime(20, speed * 45, 40);
    delayTime(21, speed * 45, 40);

    delayTime(23, speed * 45, 40);
    delayTime(24, speed * 45, 40);
    delayTime(25, speed * 45, 40);


    let path = findPath(source, sink);

    if (path) {
        bwh.classList.remove("algani");
        let i = 10;
        while (true) {
            if (i == 0) {
                bkt1.classList.add("algani");
                break;
            }
            i--;
        }

        // alert("TIM DUONG TANG LUONG MOI " + countFlow);
        possBlink = 1;
        excuteAnimationBlinkAsync();
        script.innerHTML += "<span style='font-weight:bold;color:red'>Continue traversing the vertices in the graph.This is </span>" + countFlow + "iteration of the traversal<br>";

        step_script.innerHTML = "Continue traversing the vertices in the graph. This is  " + countFlow + " iteration of the traversal<br>";
        step_script.classList.add("hightLight");
        script.style.textAlign = "left";



    } else {
        executeMinimumCut();

        alert("NOT FOUND ANY AUGUMENTING PATHS! WE WILL FIND THE MINIMUM CUT")
        document.getElementById("MaxFlowText").value = sumFlow;
        document.getElementById("path").value = countFlow;
        document.getElementById("aug").value = 0;

        delay(70, speed * 45);
        delay(71, speed * 45);
        delay(72, speed * 45);

        //Find the minimum cut from blinkVer
        //Explain:
        //blinkEdgeSoure: contain the edges from S finite to T finite
        //blinkEdgeSink: contain the edges from T finite to S finite

        blinkEdgeSource = new Queue();
        blinkEdgeSink = new Queue();

        for (let verBlinkVer of finalBlinkVer.arr) {
            console.log(verBlinkVer.id + "br");

            for (let v of mygraph.vertices) {
                if (!finalBlinkVer.arr.includes(v) && mygraph.getEdge(verBlinkVer.id, v.id) != -1) {
                    blinkEdgeSource.enqueue(mygraph.edges[mygraph.getEdge(verBlinkVer.id, v.id)]);
                }

                if (!finalBlinkVer.arr.includes(v) && mygraph.getEdge(v.id, verBlinkVer.id) != -1) {
                    blinkEdgeSink.enqueue(mygraph.edges[mygraph.getEdge(verBlinkVer.id, v.id)]);
                }

            }

        }
        console.log(" Source finite <br>");
        step_script.innerHTML = ""
        step_script.innerHTML += "Minimum cut: Source edge finite " + "<br>"
        for (let e of blinkEdgeSource.arr) {
            console.log(e.u + " " + e.v + "<br>");
            step_script.innerHTML += "(" + e.u + "," + e.v + ")" + "<br>"
        }
        step_script.innerHTML += "Minimum cut: Sink edge finite " + "<br>"
        console.log(" Sink finite <br>");
        for (let e of blinkEdgeSink.arr) {
            console.log(e.u + " " + e.v + "<br>");
            step_script.innerHTML += "(" + e.u + "," + e.v + ")" + "<br>"
        }

        for (let e of blinkEdgeSource.arr) {
            e.color = "red";
        }
        for (let e of blinkEdgeSink.arr) {
            e.color = "yellow";
        }


        step_script.innerHTML += "Found the minimum cut with the maximumflow: <br> This is the capacity of the red edge <br>";

        for (let e of blinkEdgeSource.arr) {
            step_script.innerHTML += "" + e.c + "+ "
        }

        step_script.innerHTML += " =" + sumFlow;
        mygraph.clearCanvas();
        mygraph.draw();



        ///Remove the animation "algani"
        bkt.classList.remove("algani");
        bdo.classList.remove("algani");
        bkt1.classList.remove("algani");
        blq.classList.remove("algani");
        bhx.classList.remove("algani");
        bct.classList.remove("algani");
        bcn.classList.remove("algani");
        bdt.classList.remove("algani");
        bwh.classList.remove("algani");
        btl.classList.remove("algani");
        btlct.classList.remove("algani");
        btlcn.classList.remove("algani");



        countFlow = 0;
    }

}


//find the minumumCut
const executeMinimumCut = async () => {
    try {

        const myStatus = await myBlinkVertexPromise_MinimumCut();
        console.log("find the minimum cut " + myStatus);
    } catch (err) {
        console.log("This is error: " + err);
    }
}




///#clearTableContent
function clearTableContent() {
    for (let i = 1; i <= 6; i++) {
        for (let j = 1; j <= 6; j++) {
            let idCell = "rl" + i + "v" + j;
            document.getElementById(idCell).innerHTML = "";
            document.getElementById(idCell).classList.remove("cl1-affect");
        }
        let idQueue = "rl" + i + "hd";
        document.getElementById(idQueue).innerHTML = "";
        document.getElementById(idQueue).classList.remove("cl1-affect");
    }
    for (let i = 1; i <= 6; i++) {
        for (let j = 1; j <= 8; j++) {
            let idCell = "8_rl" + i + "v" + j;
            // console.log(idCell);
            document.getElementById(idCell).innerHTML = "";
            document.getElementById(idCell).classList.remove("cl1-affect");

        }
        let idQueue = "8_rl" + i + "hd";
        document.getElementById(idQueue).innerHTML = "";
        document.getElementById(idQueue).classList.remove("cl1-affect");
    }

    step_script.innerHTML = "";
    script.innerHTML = "";
}

///#sliderFunction
///SLIDER

let slider = document.getElementById("speedSlider");
let speedValue = document.getElementById("speedValue");

speedValue.style.display = "none";




slider.oninput = function () {
    console.log(slider.value);
    speedValue.style.display = "block";
    speedValue.style.position = 'absolute';
    speedValue.value = slider.value;

    speedValue.innerHTML = speedValue.value;



    let speedV = Number.parseInt(slider.value);
    let speedLeft = 830 + speedV;


    speedValue.style.top = 100 + 'px';
    speedValue.style.textAlign = 'center';
    speedValue.style.left = speedLeft + 'px';




    speed = parseInt(slider.value);
}

slider.addEventListener("mouseup", e => {
    speedValue.style.display = "none";


    if (slider.value >= 0 && slider.value < 50) {
        let num = 100 - slider.value;

        if (num === 0) {
            speed = 100;
        } else {
            speed = num;
        }


    } else {
        let num = Math.abs(100 - slider.value);

        if (num === 0) {
            speed = 1;
        } else {
            speed = num;
        }
    }
})


///CONTENT OF ALGORITHM

let script = document.getElementById("script");
let step_script = document.getElementById("step-script");

///#PAUSE/RESUME
///PAUSE/RESUME

let isPause = false;


function pauseAnimation() {
    resumeA.disabled = false;
    resumeA.classList.remove("bg-secondary");
    resumeA.classList.add("bg-primary");

    pauseA.classList.remove("bg-primary");
    pauseA.classList.add("bg-secondary");

    pauseA.disabled = true;
    isPause = true;


}

function resumeAnmation() {
    isPause = false;
    resumeA.classList.remove("bg-primary");
    resumeA.classList.add("bg-secondary");

    pauseA.classList.remove("bg-secondary");
    pauseA.classList.add("bg-primary");

    resumeA.disabled = true;
    pauseA.disabled = false;
}


//CODE_SCRIPT
let editor = CodeMirror.fromTextArea(document.getElementById("code"), {
    lineNumbers: true,
    readOnly: true,
    mode: "javascript",
    theme: "default",
    maxHeight: "100%",
    height: "100%",
    width: "100%",
    fontSize: "5px",
    overflow: "auto",
    lineWrapping: true,

});

//set size cho đối tượng codeMirror
editor.setSize(null, 200);

function highlightLine(lineNo, delay) {
    let code = editor.getValue();
    let lines = code.split("\n");
    if (lineNo < lines.length) {
        editor.setCursor(lineNo);
        editor.addLineClass(lineNo - 1, "background", "highlight");
        editor.scrollIntoView({
            line: lineNo,
            ch: 0
        }, 50);
        //   setTimeout(function () {
        //     editor.removeLineClass(lineNo, "background", "highlight");
        //     // highlightLine(lineNo + 1, delay);
        //   }, delay);

        setTimeout(function () {
            editor.removeLineClass(lineNo - 1, "background", "highlight");
        }, delay);

    }
}


async function highlightLinesDelayed(lines, delay) {
    // const editor = CodeMirror.fromTextArea(document.getElementById("myTextarea"), {
    //   lineNumbers: true
    // });
    // editor.setValue(lines.join("\n"));

    for (const line of lines) {
        editor.setCursor(line);
        editor.addLineClass(line - 1, "background", "highlight");
        editor.scrollIntoView({
            line: line,
            ch: 0
        }, 40)
        await sleep(delay);
        editor.removeLineClass(line - 1, "background", "highlight");
    }
}

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}


//add highlight class

function addLineClass(line) {
    editor.setCursor(line);
    editor.addLineClass(line - 1, "background", "highlight");
    editor.scrollIntoView({
        line: line,
        ch: 0
    }, 50)
}

function removeLineClass(line) {
    editor.removeLineClass(line - 1, "background", "highlight");
}



function delay(line, delay) {
    let i = 40;
    while (i >= 0) {
        i--;
    }
    highlightLine(line, delay);
}

function delayTime(line, delay, time) {
    let i = time;
    while (i >= 0) {
        i--;
    }
    highlightLine(line, delay);
}