package edu.utsa.cs5363


import java.io._
import scala.io.Source
import scala.util.matching.Regex
import collection.JavaConversions._
import scala.collection.mutable.ListBuffer
object CoreCompiler {
  var counter = 0
  var regNum = 0
  var labelNum = 0
  var cfgFile = ""
  var mipsFile = ""
  var syscallRegister = "r0"
  
  var registerMap = scala.collection.mutable.HashMap.empty[String,String]
  var offSet = 0;
  
  var theMap=ListBuffer[labelledSequence]()
  def printTheMapMIPS(){
      val fileMips = new File(mipsFile)
      val writer4 = new PrintWriter(fileMips)
      writer4.write("\t\t\t\t.data\n")
      writer4.write("newline:  .asciiz \"\\n\"\n")
      writer4.write("\t\t\t\t.text\n")
      writer4.write("\t\t\t\t.globl main\n")
      writer4.write("main:\n")
      writer4.write("\t\t\t\tli $fp, 0x7ffffffc\n")
  
   for(i<-theMap.distinct.reverse){
    writer4.write(i.printMIPS()+"\n") 
   }
   writer4.close() 
  }
  
  def addToRegisterMap(registerName:String){
     if (!registerMap.contains(registerName)){
      registerMap += (registerName -> (offSet.toString()+"($fp)")) 
      offSet-=4;
     } 
  }
  
  case class register(registerName:String)
  case class label(var labelName:String)
   var labelNodeMap = scala.collection.mutable.HashMap.empty[label,String]
  def makeMap(){
        var n = -1    
        for(i<-theMap){
         labelNodeMap += {i.Label ->( "n"+(n+1).toString())}
         n=n+1
       } 
  }
  def CFGprint(CFGFile: String, theMap :ListBuffer[labelledSequence] ){
    val file = new File(CFGFile)
    val writer3 = new PrintWriter(file)
       writer3.write("digraph graphviz {\r\n")
       writer3.write("node [shape = none];\r\n")
       writer3.write("edge [tailport = s];\r\n")
       writer3.write("entry\r\n")
       writer3.write("subgraph cluster {\r\n")
       writer3.write("color=")
       writer3.write("\"/x11/white\"\r\n")

        var n = -1    
        for(i<-theMap){
         n=n+1
        } 
        for(i<-theMap){
          writer3.write(labelNodeMap(i.Label))
          writer3.write("[label=<<table border=\"0\"><tr><td border=\"1\" colspan=\"3\">")
          writer3.write((i.Label).toString())
          writer3.write("</td></tr>")
          i.returnBlocks(writer3)
        }
        writer3.write("entry->n"+n+"\r\n")
        writer3.write("}\r\n}")
        writer3.close()
        printTheMapMIPS();
  }
  def registerFactory(name:String) : register = { 
    regNum = regNum + 1
    if(name==null){
       register("r"+String.valueOf(regNum)) 
    }
    else{
       register("r"+name)
    }
  }
  
  def labelFactory() : label= { 
    labelNum = labelNum + 1
    label("L"+String.valueOf(labelNum))
  }
case class labelledSequence(var Label : label , var ILOCSeq : ListBuffer[ILOC]){
      def printMIPS():String={  
        var returnString = ""
        returnString += Label.labelName+": \n"
         for(i<-ILOCSeq){
           returnString+=("\t\t\t\t#"+i.printILOC2()+"\n")
           returnString+=(i.printMIPS()+"\n")
        }
        return returnString
      }
      def printBlock(){
         println("This is the label: "+Label)
         for(i<-ILOCSeq){
           i.printILOC()
         }
      } 
      def returnBlocks(writer3: PrintWriter){
         for(i<-ILOCSeq){
           writer3.write(i.printILOCdot())
         } 
         writer3.write("\r\n")
         for(i<-ILOCSeq){
            i.getClassName() match {
             case "cbr" =>  {        
               var condLabel = i.getLabel1()
               var elseLabel = i.getLabel2()
               if(labelNodeMap.isDefinedAt(condLabel)&& labelNodeMap.isDefinedAt(elseLabel)) {
                 writer3.write(labelNodeMap(this.Label).toString()+"->"+labelNodeMap(condLabel).toString()+"\r\n")
                 writer3.write(labelNodeMap(this.Label).toString()+"->"+labelNodeMap(elseLabel).toString()+"\r\n")
               } 
             }
             case"jumpI"=>{
               var jumpLabel = i.getLabel1()
               if(labelNodeMap.isDefinedAt(jumpLabel)){
                 writer3.write(labelNodeMap(Label)+"->"+labelNodeMap(jumpLabel)+"\r\n")
               }
             }
             case _ => {}
           } 
         }
      }
  }
  
  sealed abstract class block(){
    def getStart():labelledSequence = {println("IN ABSTRACT CLASS") 
      labelledSequence(null,null)}
    def getEnd():labelledSequence = {null}
    def getEnd2():labelledSequence = {null}
    def addToMap():Boolean = {false}
  }
  case class singleStatementBlock(var start : labelledSequence, var end : labelledSequence, var end2 : labelledSequence) extends block{
   override def getStart():labelledSequence = {//println("IN singlestatement getstart") 
     start}
   override def addToMap():Boolean = {
     theMap+=this.start
     true 
   }
  }
  case class whileStatementBlock(var start : labelledSequence, var end : labelledSequence, var end2 : labelledSequence) extends block{
    override def getStart():labelledSequence = {
      start}
    override def getEnd():labelledSequence = {end}
    override def addToMap():Boolean = { 
      theMap+=this.start
      theMap+=this.end
      true 
    }

  }
  case class ifStatementBlock(var start : labelledSequence, var end : labelledSequence, var end2 : labelledSequence) extends block{
    override def getStart():labelledSequence = {
      start}
    override def getEnd():labelledSequence = {end}
    override def getEnd2():labelledSequence = {end2}
    override def addToMap():Boolean = {
      theMap+=this.start
      theMap+=this.end
      theMap+=this.end2
      true 
    }
  }
  
    def genStmtList(code : ListBuffer[ASTStatement], otherLabel : label) : (label, block) =  {
      if(code.isEmpty()){
                  var buf = ListBuffer[ILOC]()
                  var newLabel= labelFactory()
                  buf+=jumpI(otherLabel)
                   return (newLabel, singleStatementBlock(labelledSequence(newLabel, buf),null,null))    
      }
      var ( tailLabel, tailBlock) = genStmtList(code.tail, otherLabel)
      var ( headBlock, headLabel, goto) = genStmt(code.head, tailLabel)
      headBlock match {
        case whileStatementBlock(_,_,_)=>{
          tailBlock match {
            case whileStatementBlock(_,_,_)=>{
              theMap+=tailBlock.getStart()
              theMap+=tailBlock.getEnd()
              goto.asInstanceOf[cbr].elseLabel=tailLabel
              headBlock.asInstanceOf[whileStatementBlock].start.ILOCSeq+=goto
              return (headLabel,headBlock)
            }
            case ifStatementBlock(_,_,_)=>{
              goto.asInstanceOf[cbr].elseLabel=tailLabel
              headBlock.asInstanceOf[whileStatementBlock].start.ILOCSeq+=goto
              theMap+=tailBlock.getStart()
              theMap+=tailBlock.getEnd()
              theMap+=tailBlock.getEnd2()
              return (headLabel,headBlock)
            }
            case singleStatementBlock(_,_,_)=>{
              goto.asInstanceOf[cbr].elseLabel=tailLabel
              headBlock.asInstanceOf[whileStatementBlock].start.ILOCSeq+=goto
              theMap+=tailBlock.asInstanceOf[singleStatementBlock].start
              return (headLabel,headBlock)
            }
            case _ =>{
              return(headLabel,headBlock)
            }
          }
        }
        case ifStatementBlock(_,_,_)=>{
          tailBlock match {
            case whileStatementBlock(_,_,_)=>{
              goto.asInstanceOf[jumpI].jumpLabel=tailLabel
              headBlock.getEnd().ILOCSeq+=goto
              headBlock.getEnd2().ILOCSeq+=goto
              theMap+=tailBlock.getStart()
              theMap+=tailBlock.getEnd()
              return (headLabel, headBlock)
            }
            case ifStatementBlock(_,_,_)=>{
              goto.asInstanceOf[jumpI].jumpLabel=tailLabel
              headBlock.getEnd().ILOCSeq+=goto
              headBlock.getEnd2().ILOCSeq+=goto
              theMap+=tailBlock.getStart()
              theMap+=tailBlock.getEnd()
              theMap+=tailBlock.getEnd2()
              return (headLabel,headBlock)
            }
            case singleStatementBlock(_,_,_)=>{
              goto.asInstanceOf[jumpI].jumpLabel=tailLabel
              theMap+=tailBlock.getStart()
              return (headLabel, headBlock)
            }
            case _=>{
              goto.asInstanceOf[jumpI].jumpLabel=tailLabel
              goto.asInstanceOf[jumpI].jumpLabel=tailLabel
              return (headLabel, headBlock)
            }
          }       
        }
        case singleStatementBlock(_,_,_)=>{
          tailBlock match {
            case whileStatementBlock(_,_,_)=>{
              goto.asInstanceOf[jumpI].jumpLabel=tailLabel
              headBlock.asInstanceOf[singleStatementBlock].start.ILOCSeq+=goto
              theMap+=tailBlock.getStart()
              return (headLabel , headBlock)
            }
            case ifStatementBlock(_,_,_)=>{
              goto.asInstanceOf[jumpI].jumpLabel=tailLabel
              headBlock.asInstanceOf[singleStatementBlock].start.ILOCSeq+=goto
              theMap+=tailBlock.getStart()
              return (headLabel , headBlock)
            }
            case singleStatementBlock(_,_,_)=>{
              for(i<- tailBlock.asInstanceOf[singleStatementBlock].start.ILOCSeq){
                headBlock.asInstanceOf[singleStatementBlock].start.ILOCSeq += i
              }
              return (headLabel , headBlock)   
            }
            case _ =>{
              return(headLabel,headBlock)
            }
          }          
        }
        case _ =>{
          return(null, null)
        }
      }
      
      return (null,null)
      
    }
    def genStmt(code:ASTStatement, otherLabel : label) : (block,label,ILOC) = code match {
    case ASTifStatement(nodeNum : String, cond: Expression, then: ListBuffer[ASTStatement], elsestmt: ListBuffer[ASTStatement])=>{
      var(mySeq, myRegister)=genExp(cond)
      var startLabel = labelFactory()
      var(theEndLabel, theEnd) = genStmtList(then, otherLabel)
      var(theEndLabel2, theEnd2) = genStmtList(elsestmt, otherLabel)
      if(!theEnd.addToMap() || !theEnd2.addToMap()){
        println("ATTN : Error adding to map")
      }
      var q = 0
      for(i<-elsestmt){
       q+=1
      }
      mySeq+=cbr(myRegister,theEndLabel,theEndLabel2)
      var theStart = labelledSequence(startLabel, mySeq) 
      theEnd match {
        case ifStatementBlock(_,_,_) =>{
          theEnd2 match {
            case ifStatementBlock(_,_,_) =>{
              return (ifStatementBlock(theStart, theEnd.asInstanceOf[ifStatementBlock].start, theEnd2.asInstanceOf[ifStatementBlock].start), startLabel, jumpI(null) )
            }
            case singleStatementBlock(_,_,_) =>{

              return (ifStatementBlock(theStart, theEnd.asInstanceOf[ifStatementBlock].start, theEnd2.asInstanceOf[singleStatementBlock].start), startLabel, jumpI(null) )
            }
            case whileStatementBlock(_,_,_) =>{
              return (ifStatementBlock(theStart, theEnd.asInstanceOf[ifStatementBlock].start, theEnd2.asInstanceOf[whileStatementBlock].start), startLabel, jumpI(null) )
            }
          }
        }
        case singleStatementBlock(_,_,_) =>{
          theEnd2 match {
            case ifStatementBlock(_,_,_) =>{
              return (ifStatementBlock(theStart, theEnd.asInstanceOf[singleStatementBlock].start, theEnd2.asInstanceOf[ifStatementBlock].start), startLabel, jumpI(null) )
            }
            case singleStatementBlock(_,_,_) =>{
              return (ifStatementBlock(theStart, theEnd.asInstanceOf[singleStatementBlock].start, theEnd2.asInstanceOf[singleStatementBlock].start), startLabel, jumpI(null) )
            }
            case whileStatementBlock(_,_,_) =>{
              return (ifStatementBlock(theStart, theEnd.asInstanceOf[singleStatementBlock].start, theEnd2.asInstanceOf[whileStatementBlock].start), startLabel, jumpI(null) )
            }
          }
        }
        case whileStatementBlock(_,_,_) =>{
          theEnd2 match {
            case ifStatementBlock(_,_,_) =>{
              return (ifStatementBlock(theStart, theEnd.asInstanceOf[whileStatementBlock].start, theEnd2.asInstanceOf[ifStatementBlock].start), startLabel, jumpI(null) )
            }
            case singleStatementBlock(_,_,_) =>{
              return (ifStatementBlock(theStart, theEnd.asInstanceOf[whileStatementBlock].start, theEnd2.asInstanceOf[singleStatementBlock].start), startLabel, jumpI(null) )
            }
            case whileStatementBlock(_,_,_) =>{
              return (ifStatementBlock(theStart, theEnd.asInstanceOf[whileStatementBlock].start, theEnd2.asInstanceOf[whileStatementBlock].start), startLabel, jumpI(null) )
            }
          }
        }

      }
      println("DID NOT FIND MATCH*****************************************")
      return null 
    }
     case ASTStatementDecl(_,_,_) =>{
       code.asInstanceOf[ASTStatementDecl].variableName.nodeNum="n"+globalCounter
       globalCounter += 1
      var(mySeq, myRegister)= genExp(code.asInstanceOf[ASTStatementDecl].variableName)
      var startLabel = labelFactory()
      var A = mySeq
      code.asInstanceOf[ASTStatementDecl].varType match {
        case ASTInt(_) =>{
          A += loadI(0,myRegister)
        }
        case ASTBool(_) =>{
         A += loadIBool("false",myRegister) 
        }
        case _ =>{
          
        }
      }
      var myLabelledSequence = labelledSequence(startLabel, A)
      return (singleStatementBlock(myLabelledSequence, null, null), startLabel,jumpI(null))  
    }
    case(ASTwhileStatement(nodeNum : String, cond: Expression , loop :ListBuffer[ASTStatement]))=>{
      var(mySeq, myRegister)=genExp(cond)
      var startLabel = labelFactory()     
      var(theEndLabel, theEnd) = genStmtList(loop, startLabel)
      var theStart = labelledSequence(startLabel, mySeq) 
      theEnd.addToMap()
  
      theEnd match {
            case ifStatementBlock(start : labelledSequence, end : labelledSequence, end2 : labelledSequence) =>{
              return (whileStatementBlock(theStart, theEnd.asInstanceOf[ifStatementBlock].start, null), startLabel, cbr(myRegister,theEndLabel,label("NONE"))) 
            }
            case singleStatementBlock(start : labelledSequence, end : labelledSequence, end2 : labelledSequence) =>{
              return (whileStatementBlock(theStart, theEnd.asInstanceOf[singleStatementBlock].start, null), startLabel, cbr(myRegister,theEndLabel,label("NONE"))) 
            }
            case whileStatementBlock(start : labelledSequence, end : labelledSequence, end2 : labelledSequence) =>{
              return (whileStatementBlock(theStart, theEnd.asInstanceOf[whileStatementBlock].start, null), startLabel, cbr(myRegister,theEndLabel,label("NONE"))) 
            }
            case _ =>{
                    return (whileStatementBlock(theStart, theEnd.getStart(), null), startLabel, cbr(myRegister,theEndLabel,label("NONE")))
            }
      }
    } 
     case(ASTassignment(nodeNum : String, variableName: Expression, expr: Expression)) =>{
        var(leftSeq, leftRegister)=genExp(variableName)
        var(rightSeq, rightRegister)=genExp(expr)
        var startLabel = labelFactory()
        var A = rightSeq :+ i2i(leftRegister,rightRegister)
        var myLabelledSequence = labelledSequence(startLabel, A)
        return (singleStatementBlock(myLabelledSequence, null, null), startLabel,jumpI(null))     
    } 

    case(ASTAssignReadInt(nodeNum : String, variableName: Identifier))=>{
       var(mySeq, myRegister)=genExp(variableName)
       var startLabel = labelFactory()
       var A = mySeq :+ ILOCreadInt(myRegister)
       var myLabelledSequence = labelledSequence(startLabel, A)
       return (singleStatementBlock(myLabelledSequence, null, null), startLabel,jumpI(null)) 
      }
      
      
      case(ASTwriteInt(nodeNum : String, expr : Expression)) =>{
      var(mySeq, myRegister)=genExp(expr)
      var startLabel = labelFactory()
      var A = mySeq :+ ILOCwriteInt(myRegister)
      var myLabelledSequence = labelledSequence(startLabel, A)
      return (singleStatementBlock(myLabelledSequence, null, null), startLabel,jumpI(null)) 
      
      }
    return (null,null,null)
  } 
 sealed abstract class ILOC{
    def printILOC(){println("abstract version only")}
    def printILOCdot():String={return ("abstract version only")}
    def getLabel1(): label = {return label("constructor")}
    def getLabel2(): label = {return label("constructor")}
    def getClassName() : String = {return "test"}
    def printMIPS():String={return("\t\t\t\tThis is abstract MIPSILOC")}
    def printILOC2():String={return("This is the abstract printILOC2")}
  }
  case class EXITILOC(labelFrom:String) extends ILOC{ 
    override def printILOCdot():String={return("<tr><td align=\"left\">Exit</td></tr></table>>,fillcolor=\"/x11/white\",shape=box]\n"+labelFrom+"->Exit")}
    override def printILOC2():String={return("exit")}
    override def printMIPS():String={
     return ("\t\t\t\tli $v0, 10\n\t\t\t\tsyscall ")  
    }
  }
  case class FORTESTINGONLY() extends ILOC{
   override def printILOC(){println("FOR TESTING ONLY PRINT")} 
   override def printILOCdot():String =  {return ("FOR TESTING ONLY PRINT")}
   override def printMIPS():String={return("\t\t\t\tThis is TEST MIPSILOC")}
  }
  case class loadI(number:Integer, myRegister:register) extends ILOC{
   override def printILOC(){println("loadI "+number.toString()+"=>"+myRegister.registerName)}
   override def printILOC2():String={return("loadI "+number.toString()+"=>"+myRegister.registerName)}
   override def printILOCdot():String={return("<tr><td align=\"left\">loadI</td><td align=\"left\">"+number.toString()+"</td><td align=\"left\">=&gt;"+myRegister.registerName+"</td></tr>")}
   override def printMIPS() : String = {
    addToRegisterMap(myRegister.registerName)
    var strLoad = "\t\t\t\tli $t0, "+number.toString()+"\r\n"+"\t\t\t\tsw $t0, "+registerMap(myRegister.registerName)+"\r\n"
    return strLoad
   }
  }
  case class i2i(left:register, right:register) extends ILOC{
    override def printILOC(){println("i2i "+right.registerName+"=>"+left.registerName)}
    override def printILOC2():String={return("i2i "+right.registerName+"=>"+left.registerName)}
    override def printILOCdot():String={return("<tr><td align=\"left\">i2i</td><td align=\"left\">"+right.registerName+"</td><td align=\"left\">=&gt;"+left.registerName+"</td></tr>")}
    override def printMIPS(): String = {
      var stri2i = "\t\t\t\tlw $t1, "+registerMap(right.registerName)+"\r\n"+
                   "\t\t\t\tadd $t0, $t1, $zero \r\n"+"\t\t\t\tsw $t0, "+registerMap(left.registerName)+"\r\n"
      return stri2i 
    }
  }
  case class loadIBool(Boolit:String, myRegister:register) extends ILOC{
   override def printILOC(){println("LoadI "+Boolit.toString()+"=>"+myRegister.registerName)}
   override def printILOC2():String={return("LoadI "+Boolit.toString()+"=>"+myRegister.registerName)}
   override def printILOCdot():String={return("<tr><td align=\"left\">loadI</td><td align=\"left\">"+Boolit.toString()+"</td><td align=\"left\">=&gt;"+myRegister.registerName+"</td></tr>")}
   override def printMIPS() : String = {
    addToRegisterMap(myRegister.registerName)
    var BoolitValue = 0 
    if(Boolit.equals(true)){
      BoolitValue = 1
    }
    else{
      BoolitValue = 0 
    }
    var strLoad = "\t\t\t\tli $t0, "+BoolitValue.toString()+"\r\n"+"\t\t\t\tsw $t0, "+registerMap(myRegister.registerName)+"\r\n"
    return strLoad
   }
  }
  case class add(left:register,right:register,outputRegister:register) extends ILOC{
    override def printILOC(){println("add "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOC2():String={return("add "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOCdot():String={return("<tr><td align=\"left\">add</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>")}
    override def printMIPS():String={
        addToRegisterMap(left.registerName)
        addToRegisterMap(right.registerName)
        addToRegisterMap(outputRegister.registerName)
        var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
        returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
        returnValue += ("\t\t\t\taddu $t0, $t1, $t2\n")
        returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
        addToRegisterMap(outputRegister.registerName)
        return returnValue
    }   
  }
  case class sub(left:register,right:register,outputRegister:register) extends ILOC{
    override def printILOC(){println("sub "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOC2():String={return("sub "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOCdot():String={return("<tr><td align=\"left\">sub</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>")}
    override def printMIPS():String={
        addToRegisterMap(left.registerName)
        addToRegisterMap(right.registerName)
        addToRegisterMap(outputRegister.registerName)
        var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
        returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
        returnValue += ("\t\t\t\tsubu $t0, $t1, $t2\n")
        returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
        addToRegisterMap(outputRegister.registerName)
        return returnValue
    }  
  }
  
  case class div(left:register,right:register,outputRegister:register) extends ILOC{
    override def printILOC(){println("div "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOC2():String={return("div "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOCdot():String={return("<tr><td align=\"left\">div</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>")}
    override def printMIPS():String={
        addToRegisterMap(left.registerName)
        addToRegisterMap(right.registerName)
        addToRegisterMap(outputRegister.registerName)
        var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
        returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
        returnValue += ("\t\t\t\tdiv $t0, $t1, $t2\n")
        returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
        addToRegisterMap(outputRegister.registerName)
        return returnValue
    } 
  }
  case class mult(left:register,right:register,outputRegister:register) extends ILOC{
    override def printILOC(){println("mult "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOC2():String={return("mult "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOCdot():String={return("<tr><td align=\"left\">mult</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>")}
    override def printMIPS():String={
        addToRegisterMap(left.registerName)
        addToRegisterMap(right.registerName)
        addToRegisterMap(outputRegister.registerName)
        var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
        returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
        returnValue += ("\t\t\t\tmul $t0, $t1, $t2\n")
        returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
        return returnValue
    } 
  }
  case class mod(left:register,right:register,outputRegister:register) extends ILOC{
    override def printILOC(){
      println("div "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)
      println("mult "+outputRegister.registerName+","+right.registerName+"=>"+outputRegister.registerName)
      println("sub "+left.registerName+","+outputRegister.registerName+"=>"+outputRegister.registerName)  
    }
    override def printILOC2():String={return("mod "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOCdot():String ={
      var A = "<tr><td align=\"left\">div</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>"
      A+="<tr><td align=\"left\">mult</td><td align=\"left\">"+outputRegister.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>"
      A+="<tr><td align=\"left\">sub</td><td align=\"left\">"+left.registerName+","+outputRegister.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>"
      return A
    }
    override def printMIPS():String={
        addToRegisterMap(left.registerName)
        addToRegisterMap(right.registerName)
        addToRegisterMap(outputRegister.registerName)
        //Div below
        var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
        returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
        returnValue += ("\t\t\t\tdivu $t0, $t1, $t2\n")    
        //Mult below
        returnValue += ("\t\t\t\tmul $t0, $t0, $t2\n")
        //Subtract below
        returnValue += ("\t\t\t\tsubu $t0, $t1, $t0\n")
        //Store result
        returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
        return returnValue
    } 
  }
  case class ILOCreadInt(myRegister:register) extends ILOC{
   override def printILOC(){println("readInt=>"+ myRegister.registerName)}
   override def printILOC2():String={return("readInt=>"+ myRegister.registerName)}
   override def printILOCdot():String = {return("<tr><td align=\"left\">readInt</td><td align=\"left\">=&gt;"+myRegister.registerName+"</td></tr>")}
   override def printMIPS() : String = {
        addToRegisterMap(myRegister.registerName)
        var returnValue = ("\t\t\t\tli $v0, 5\n")   
        returnValue += ("\t\t\t\tsyscall\n")
        returnValue += ("\t\t\t\tadd $t0, $v0, $zero\n")
        returnValue += ("\t\t\t\tsw $t0, "+registerMap(myRegister.registerName)+"\n")
        return returnValue
   }
  }
  case class ILOCwriteInt(myRegister:register) extends ILOC{
   override def printILOC(){println("writeInt=>"+ myRegister)}
   override def printILOC2():String={return("writeInt=>"+ myRegister)}
   override def printILOCdot():String = {return("<tr><td align=\"left\">writeInt</td><td align=\"left\">=&gt;"+myRegister.registerName+"</td></tr>")}
   override def printMIPS() : String = {
        addToRegisterMap(myRegister.registerName)
        var returnValue = ("\t\t\t\tli $v0, 1\n")  
        returnValue += ("\t\t\t\tlw $t1, "+registerMap(myRegister.registerName)+"\n")
        returnValue += ("\t\t\t\tadd $a0, $t1, $zero\n")
        returnValue += ("\t\t\t\tsyscall\n")
        returnValue += ("\t\t\t\tli $v0, 4\n")
        returnValue += ("\t\t\t\tla $a0, newline\n")
        returnValue += ("\t\t\t\tsyscall\n")
        return returnValue
   }

  }
  case class lte(left:register,right:register,outputRegister:register) extends ILOC{
   override def printILOC(){println("cmp_LTE "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)} 
   override def printILOC2():String={return("cmp_LTE "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
   override def printILOCdot(): String = {return("<tr><td align=\"left\">cmp_LTE</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>")}
   override def printMIPS() : String = {
     addToRegisterMap(left.registerName)
     addToRegisterMap(right.registerName)
     addToRegisterMap(outputRegister.registerName)
     var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
     returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
     returnValue += ("\t\t\t\tsle $t0, $t1, $t2\n")
     returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
     return returnValue
   }
  }
  case class lt(left:register,right:register,outputRegister:register) extends ILOC{
    override def printILOC(){println("cmp_LT "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOC2():String={return("cmp_LT "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
    override def printILOCdot():String = {return("<tr><td align=\"left\">cmp_LT</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>")} 
    override def printMIPS() : String = {
     addToRegisterMap(left.registerName)
     addToRegisterMap(right.registerName)
     addToRegisterMap(outputRegister.registerName)
     var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
     returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
     returnValue += ("\t\t\t\tslt $t0, $t1, $t2\n")
     returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
     return returnValue
   }
  }
  case class gte(left:register,right:register,outputRegister:register) extends ILOC{
   override def printILOC(){println("cmp_GTE "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)} 
   override def printILOC2():String={return("cmp_GTE "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
   override def printILOCdot(): String = {return("<tr><td align=\"left\">cmp_GTE</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>")}
   override def printMIPS() : String = {
     addToRegisterMap(left.registerName)
     addToRegisterMap(right.registerName)
     addToRegisterMap(outputRegister.registerName)
     var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
     returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
     returnValue += ("\t\t\t\tsge $t0, $t1, $t2\n")
     returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
     return returnValue
   }
  }
  case class gt(left:register,right:register,outputRegister:register) extends ILOC{
   override def printILOC(){println("cmp_GT "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)} 
   override def printILOC2():String={return("cmp_GT "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
   override def printILOCdot(): String = {return("<tr><td align=\"left\">cmp_GT</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>")}
   override def printMIPS() : String = {
     addToRegisterMap(left.registerName)
     addToRegisterMap(right.registerName)
     addToRegisterMap(outputRegister.registerName)
     var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
     returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
     returnValue += ("\t\t\t\tsgt $t0, $t1, $t2\n")
     returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
     return returnValue
   }
  }
  case class eq(left:register,right:register,outputRegister:register) extends ILOC{
   override def printILOC(){println("cmp_EQ "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)} 
   override def printILOC2():String={return("cmp_EQ "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
   override def printILOCdot(): String = {return("<tr><td align=\"left\">cmp_EQ</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>")}
   override def printMIPS() : String = {
     addToRegisterMap(left.registerName)
     addToRegisterMap(right.registerName)
     addToRegisterMap(outputRegister.registerName)
     var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
     returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
     returnValue += ("\t\t\t\tseq $t0, $t1, $t2\n")
     returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
     return returnValue
   }
 }
  case class neq(left:register,right:register,outputRegister:register) extends ILOC{
   override def printILOC(){println("cmp_NE "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)} 
   override def printILOC2():String={return("cmp_NE "+left.registerName+","+right.registerName+"=>"+outputRegister.registerName)}
   override def printILOCdot(): String = {return("<tr><td align=\"left\">cmp_NE</td><td align=\"left\">"+left.registerName+","+right.registerName+"</td><td align=\"left\">=&gt;"+outputRegister.registerName+"</td></tr>")}
   override def printMIPS() : String = {
     addToRegisterMap(left.registerName)
     addToRegisterMap(right.registerName)
     addToRegisterMap(outputRegister.registerName)
     var returnValue = ("\t\t\t\tlw $t1, "+registerMap(left.registerName)+"\n")
     returnValue += ("\t\t\t\tlw $t2, "+registerMap(right.registerName)+"\n")
     returnValue += ("\t\t\t\tsne $t0, $t1, $t2\n")
     returnValue += ("\t\t\t\tsw $t0, "+registerMap(outputRegister.registerName)+"\n")
     return returnValue
   }
  }
  case class cbr(myRegister:register,condLabel:label,var elseLabel:label) extends ILOC{
    override def printILOC(){println("cbr "+myRegister.registerName+"->"+condLabel.labelName+","+elseLabel.labelName)}
    override def printILOC2():String={return("cbr "+myRegister.registerName+"->"+condLabel.labelName+","+elseLabel.labelName)}
    override def printILOCdot(): String = 
    {
      return("<tr><td align=\"left\">cbr</td><td align=\"left\">"+myRegister.registerName+"</td><td align=\"left\">-&gt;"+condLabel.labelName+","+elseLabel.labelName+"</td></tr></table>>,fillcolor=\"/x11/white\",shape=box]")
    }
    override def getLabel1():label = {return (condLabel)}
    override def getLabel2():label = {return (elseLabel)}
    override def getClassName(): String = {return "cbr"}
    override def printMIPS() : String = {
     addToRegisterMap(myRegister.registerName)
     var returnValue = ("\t\t\t\tlw $t0, "+registerMap(myRegister.registerName)+"\n")     
     returnValue += ("\t\t\t\tbne $t0, $zero, "+condLabel.labelName+"\n")
     returnValue += ("\t\t\t\tj "+elseLabel.labelName+"\n")
     return returnValue
   }
  }
  case class jumpI(var jumpLabel:label) extends ILOC{
    override def printILOC(){println("jumpI ->"+jumpLabel.labelName)}
    override def printILOC2():String={return("jumpI ->"+jumpLabel.labelName)}
    override def printILOCdot(): String = {
      return("<tr><td align=\"left\">jumpI</td><td align=\"left\"></td><td align=\"left\">-&gt;"+jumpLabel.labelName+"</td></tr></table>>,fillcolor=\"/x11/white\",shape=box]")
    }
    override def getLabel1(): label = {return (jumpLabel)}
    override def getClassName(): String = {return "jumpI"}
    override def printMIPS() : String = {return("\t\t\t\tj "+jumpLabel.labelName+"\n")}
  }
  def genExp(ast:Expression):(ListBuffer[ILOC], register)=ast match{
    case Identifier(nodeNum : String, value : String)=>{
      var freshRegister = registerFactory(value)
      return (ListBuffer(), freshRegister)
    }
    case Number(nodeNum : String, value : Integer)=>{
      var freshRegister = registerFactory(null)
      var myLoadI = loadI(ast.asInstanceOf[Number].value, freshRegister)
      return (ListBuffer(myLoadI), freshRegister)
    }
    case Boolliteral(nodeNum : String, value : String)=>{
      var freshRegister = registerFactory(null)
      var myLoadI = loadIBool(ast.asInstanceOf[Boolliteral].value, freshRegister)
      return (ListBuffer(myLoadI), freshRegister)
    }
    case ASTCompare(nodeNum : String, compType: String, left: Expression, right: Expression)=>{
      //println(ast.asInstanceOf[ASTCompare].compType)
      var freshRegister = registerFactory(null)
      var(leftInst, leftRegister)=genExp(left)
      var(rightInst, rightRegister)=genExp(right)
      var inst = ast.asInstanceOf[ASTCompare].compType match {
        case "<=" =>{
          //println("inside of compare ")
         return (leftInst++rightInst++ListBuffer(lte(leftRegister, rightRegister, freshRegister)), freshRegister)
        }    
        case ">=" =>{
         return (leftInst++rightInst++ListBuffer(gte(leftRegister, rightRegister, freshRegister)), freshRegister)
        }    
        case "<" =>{
          return (leftInst++rightInst++ListBuffer(lt(leftRegister, rightRegister, freshRegister)), freshRegister)
        }    
        case ">" =>{
          return (leftInst++rightInst++ListBuffer(gt(leftRegister, rightRegister, freshRegister)), freshRegister)
        }
        case "=" =>{
         return (leftInst++rightInst++ListBuffer(eq(leftRegister, rightRegister, freshRegister)), freshRegister) 
        }
        case "!=" =>{
         return (leftInst++rightInst++ListBuffer(neq(leftRegister, rightRegister, freshRegister)), freshRegister)
        }
      }
      (ListBuffer(FORTESTINGONLY()),registerFactory("fortestingonly"))
    }
    case ASTMultiply(nodeNum : String, left: Expression, right: Expression) =>{
      var freshRegister = registerFactory(null)
      var(leftInst, leftRegister)=genExp(left)
      var(rightInst, rightRegister)=genExp(right)
      return (leftInst++rightInst++ListBuffer(mult(leftRegister, rightRegister, freshRegister)), freshRegister)
    }
    case ASTDivision(nodeNum : String, left: Expression, right: Expression) =>{
      var freshRegister = registerFactory(null)
      var(leftInst, leftRegister)=genExp(left)
      var(rightInst, rightRegister)=genExp(right)
      return (leftInst++rightInst++ListBuffer(div(leftRegister, rightRegister, freshRegister)), freshRegister)
    }
    case ASTMod(nodeNum : String, left: Expression, right: Expression) =>{
      var freshRegister = registerFactory(null)
      var(leftInst, leftRegister)=genExp(left)
      var(rightInst, rightRegister)=genExp(right)
      return (leftInst++rightInst++ListBuffer(mod(leftRegister, rightRegister, freshRegister)), freshRegister)
    }
    case ASTAddition(nodeNum : String, left: Expression, right: Expression) =>{
      var freshRegister = registerFactory(null)
      var(leftInst, leftRegister)=genExp(left)
      var(rightInst, rightRegister)=genExp(right)
      return (leftInst++rightInst++ListBuffer(add(leftRegister, rightRegister, freshRegister)), freshRegister)
    }
    case ASTSubtract(nodeNum : String, left: Expression, right: Expression) =>{
      var freshRegister = registerFactory(null)
      var(leftInst, leftRegister)=genExp(left)
      var(rightInst, rightRegister)=genExp(right)
      return (leftInst++rightInst++ListBuffer(sub(leftRegister, rightRegister, freshRegister)), freshRegister)
    }
    (ListBuffer(FORTESTINGONLY()),registerFactory("fortestingonly"))
  }
  sealed abstract class Program {
       def print(ASTFile:String){println("test2")}
       def typeCheck(writer2:PrintWriter):Boolean={true}
       
  }
  case class Start(var nodeNum : String, decl: ListBuffer[ASTDeclarations], body: ListBuffer[ASTStatement]) extends Program{
     override def print(ASTFile:String){
       //println("in print now")
       var parent = "n" + globalCounter
       val writer2 = new PrintWriter(new File(ASTFile))
       writer2.write("digraph parseTree {\n")
       writer2.write("ordering=out;\n")
       writer2.write("node [shape = box, style = filled];\n")
       nodeNum=printParseTree1("Start", null , writer2,null)
       if(!decl.isEmpty){
         var decllistId=printParseTree1("stmt list", parent , writer2,null)
         for(i<-decl: ListBuffer[ASTDeclarations]){
           i.print(decllistId, writer2)
         }
       }
       if(!body.isEmpty){
         var smntlistId=printParseTree1("stmt list", parent , writer2,null)
         for(i<-body: ListBuffer[ASTStatement]){
           i.print(smntlistId, writer2)
         }
       }
       try{
         this.typeCheck(writer2)

       }
       catch{
        case e: ASTError =>{
          println(e.getMessage)
         } 
       }
       writer2.write("}\n")
       writer2.close()
   }  
   override def typeCheck(writer2:PrintWriter):Boolean={
     var typeOkDecls = true
     for(i<-decl){
      if(!i.typeCheck(writer2)){
       typeOkDecls = false 
      } 
     }
     var typeOkStatements = true
     for(i<-body){
      if(!i.typeCheck(writer2)){
       typeOkDecls = false 
      } 
     }
     if(!(typeOkStatements && typeOkDecls)){
      changeNodeColor(nodeNum,writer2,"/pastel13/1") 
     }
     var programOk=(typeOkStatements && typeOkDecls)
     if(programOk){
            var convertDecls = ListBuffer[ASTStatementDecl]()
            for(i<-decl){
              var numberID="n"+globalCounter
              globalCounter+=1
               convertDecls+=ASTStatementDecl(numberID,i.asInstanceOf[ASTdecl].variableName, i.asInstanceOf[ASTdecl].varType)   
            }
           var (myLabels, myStart) = genStmtList(convertDecls++=:this.body,label("Exit"))
           var index = 0;
           var changeMe=ListBuffer[ILOC](jumpI(label("NONE")))
           myStart.addToMap()
           makeMap()
           for (i<-theMap){
            for(j<-i.ILOCSeq){
             j match {
               case jumpI(_)=>{
                if (j.asInstanceOf[jumpI].jumpLabel.equals(label("Exit"))){
                  i.ILOCSeq-=j
                  i.ILOCSeq+=EXITILOC(labelNodeMap(i.Label)) 
                }
               } 
               case _ => {}
             } 
            } 
            index += 1
           } 
           CoreCompiler.CFGprint(cfgFile, theMap.distinct)
           true 
     }
     else{
       throw ASTError("TYPE ERROR")
     }
   }
  }
  sealed abstract class ASTDeclarations(){
    def print(parent : String, writer2 :PrintWriter){println("test")}
    def typeCheck(writer2:PrintWriter) : Boolean = {true}
  }
  case class ASTdecl(var nodeNum : String, variableName : Identifier, varType : Type) extends ASTDeclarations{
   override def print(parent : String, writer2 :PrintWriter){
     nodeNum=variableName.printForType(parent,writer2)
     varType.print(nodeNum,writer2)
   } 
   override def typeCheck(writer2:PrintWriter) : Boolean={
     if(map(variableName.value)==varType.typeCheck(writer2)){
       if(map(variableName.value)=="INT"){
        changeNodeColor(nodeNum, writer2, "/pastel13/3") 
       }
       else{
         changeNodeColor(nodeNum, writer2, "/pastel13/2")
       }
       true
     }
     else{ 
       changeNodeColor(nodeNum, writer2, "/pastel13/1")
       false
     }
   }
  } 
  sealed abstract class Type{
   def print(parent : String, writer2 :PrintWriter){println("test")}
   def typeCheck(writer2:PrintWriter) : String = {""}
  }
  case class ASTInt(var nodeNum : String) extends Type{
    override def print(parent : String, writer2 :PrintWriter){
      nodeNum=printParseTree1("int", parent , writer2, null)
    }
    override def typeCheck(writer2:PrintWriter) : String = "INT" 
  }
  case class ASTBool(var nodeNum : String) extends Type{
    override def print(parent : String, writer2 :PrintWriter){
      nodeNum=printParseTree1("bool", parent , writer2, null)
    }
    override def typeCheck(writer2:PrintWriter) : String = "BOOL"
  }
  sealed abstract class ASTStatement{
    def print(parent : String, writer2 :PrintWriter){println("test")}
    def typeCheck(writer2:PrintWriter) : Boolean = {true}
  }
  case class ASTStatementDecl(var nodeNum : String, variableName : Identifier, varType : Type) extends ASTStatement{}
  case class ASTassignment(var nodeNum : String, variableName: Expression, expr: Expression) extends ASTStatement{
   override def print(parent : String, writer2 :PrintWriter){
     nodeNum=printParseTree1(":=", parent , writer2,null)
     variableName.print( nodeNum,writer2)
     expr.print( nodeNum,writer2)
   } 
   override def typeCheck(writer2:PrintWriter) : Boolean ={
    if(variableName.typeCheck(writer2) == expr.typeCheck(writer2)  ){
      true
    }
    else{
      changeNodeColor(nodeNum, writer2, "/pastel13/1")
      false
    }
   }
  }
  case class ASTAssignReadInt(var nodeNum : String, variableName: Identifier) extends ASTStatement{
   override def print(parent : String, writer2 :PrintWriter){
     nodeNum=printParseTree1(":= readInt", parent , writer2,null)
     variableName.print( nodeNum,writer2)
   } 
   override def typeCheck(writer2:PrintWriter) : Boolean ={
    if(map.contains(variableName.value)){
      if(map(variableName.value)== "INT"){
        changeNodeColor(variableName.nodeNum, writer2, "/pastel13/3")
        true
      }
      else{
       changeNodeColor(variableName.nodeNum, writer2, "/pastel13/2") 
       changeNodeColor(nodeNum, writer2, "/pastel13/1") 
       false
      } 
    }
    else{
     changeNodeColor(variableName.nodeNum, writer2, "/pastel13/1")
     false
    }
   }
  }
  case class ASTifStatement(var nodeNum : String, cond: Expression, then: ListBuffer[ASTStatement], elsestmt: ListBuffer[ASTStatement]) extends ASTStatement{
   override def print(parent : String, writer2 :PrintWriter){
     nodeNum=printParseTree1("if", parent , writer2,null)
     cond.print( nodeNum, writer2)
     if(!then.isEmpty){
       var thenId=printParseTree1("stmt list", nodeNum , writer2,null)
       for(i<-then: ListBuffer[ASTStatement]){
         i.print(thenId, writer2)
       }
     }
     if(!then.isEmpty){
       var elseId=printParseTree1("stmt list", nodeNum , writer2,null)
       for(i<-elsestmt: ListBuffer[ASTStatement]){
         i.print(elseId, writer2)
       }
     }

   }
   override def typeCheck(writer2:PrintWriter) : Boolean ={
    var typeCond = cond.typeCheck(writer2)
    var typeThen = true
    var typeElse = true
     for(i<-then){
      if(!i.typeCheck(writer2)){
      typeThen  = false 
      } 
     }
     for(i<-elsestmt){
      if(!i.typeCheck(writer2)){
      typeElse = false 
      } 
     }
     var typeIfStmt = ((typeCond == "BOOL") && typeThen && typeElse)
     if(!typeIfStmt){
       changeNodeColor(nodeNum, writer2, "/pastel13/1")
     }  
     typeIfStmt
   }
  } 
  case class ASTwhileStatement(var nodeNum : String, cond: Expression , loop :ListBuffer[ASTStatement] ) extends ASTStatement{
   override def print(parent : String, writer2 :PrintWriter){
     nodeNum=printParseTree1("while", parent , writer2,null)
     cond.print( nodeNum, writer2)
     if(!loop.isEmpty){
       var loopId=printParseTree1("stmt list", nodeNum , writer2,null)
       for(i<-loop: ListBuffer[ASTStatement]){
         i.print(loopId, writer2)
       }
     }
   } 
   override def typeCheck(writer2:PrintWriter) : Boolean ={
    var typeCond = cond.typeCheck(writer2)
    var typeThen = true
    var typeElse = true
     for(i<-loop){
      if(!i.typeCheck(writer2)){
      typeThen  = false 
      } 
     }
     var typeIfStmt = ((typeCond == "BOOL") && typeThen && typeElse)
     if(!typeIfStmt){
       changeNodeColor(nodeNum, writer2, "/pastel13/1")
     }
     typeIfStmt    
   }
  }
  case class ASTwriteInt(var nodeNum : String, expr : Expression) extends ASTStatement{
   override def print(parent : String, writer2 :PrintWriter){
     nodeNum =printParseTree1("writeInt", parent , writer2,null)
     expr.print( nodeNum,writer2)
   } 
      override def typeCheck(writer2:PrintWriter) : Boolean ={
        if(expr.typeCheck(writer2)=="INT"){     
          true
        }
        else{
          changeNodeColor(nodeNum, writer2, "/pastel13/1")          
          false
        }
      }
  }
  sealed abstract class Expression{
   def print(parent : String, writer2 :PrintWriter){println("test")}
   def typeCheck(writer2:PrintWriter) : String = {""}
  }
  case class ASTCompare(var nodeNum : String, compType: String, left: Expression, right: Expression) extends Expression{
    override def print(parent : String, writer2 :PrintWriter){
     nodeNum=printParseTree1(compType, parent , writer2,null)
     left.print( nodeNum,writer2)
     right.print( nodeNum, writer2)
   } 
   override def typeCheck(writer2:PrintWriter) : String ={
    var leftType = left.typeCheck(writer2)
    var rightType = right.typeCheck(writer2)
    if(leftType == "INT" && rightType == "INT"){
      changeNodeColor(nodeNum, writer2, "/pastel13/2")
      "BOOL"
    }
    else{
      changeNodeColor(nodeNum, writer2, "/pastel13/1")
      "BROKEN"
    }
   }    
  }
  case class ASTMultiply(var nodeNum : String, left: Expression, right: Expression) extends Expression{
   override def print(parent : String, writer2 :PrintWriter){
     nodeNum=printParseTree1("*", parent , writer2,null)  
     left.print( nodeNum,writer2)
     right.print( nodeNum, writer2)
   } 
   override def typeCheck(writer2:PrintWriter) : String ={
    var leftType = left.typeCheck(writer2)
    var rightType = right.typeCheck(writer2)
    if(leftType == "INT" && rightType == "INT"){
      changeNodeColor(nodeNum, writer2, "/pastel13/3")
      leftType
    }
    else{
      changeNodeColor(nodeNum, writer2, "/pastel13/1")
      "BROKEN"
    }
   }
  }
  case class ASTMod(var nodeNum : String, left: Expression, right: Expression) extends Expression{
   override def print(parent : String, writer2 :PrintWriter){
     nodeNum=printParseTree1("%", parent , writer2,null)  
     left.print( nodeNum,writer2)
     right.print( nodeNum, writer2)
   } 
   override def typeCheck(writer2:PrintWriter) : String ={
    var leftType = left.typeCheck(writer2)
    var rightType = right.typeCheck(writer2)
    if(leftType == "INT" && rightType == "INT"){
      changeNodeColor(nodeNum, writer2, "/pastel13/3")
      leftType
    }
    else{
      changeNodeColor(nodeNum, writer2, "/pastel13/1")
      "BROKEN"
    }
   }
  }
  case class ASTDivision(var nodeNum : String, left: Expression, right: Expression) extends Expression{
   override def print(parent : String, writer2 :PrintWriter){
     nodeNum=printParseTree1("/", parent , writer2,null)  
     left.print( nodeNum,writer2)
     right.print( nodeNum, writer2)
   } 
   override def typeCheck(writer2:PrintWriter) : String ={
    var leftType = left.typeCheck(writer2)
    var rightType = right.typeCheck(writer2)
    if(leftType == "INT" && rightType == "INT"){
      changeNodeColor(nodeNum, writer2, "/pastel13/3")
      leftType
    }
    else{
      changeNodeColor(nodeNum, writer2, "/pastel13/1")
      "BROKEN"
    }
   }
  }
  case class ASTAddition(var nodeNum : String, left: Expression, right: Expression) extends Expression{
   override def print(parent : String, writer2 :PrintWriter){
      nodeNum=printParseTree1("+", parent , writer2,null)
     left.print( nodeNum,writer2)
     right.print( nodeNum, writer2)

   }  
   override def typeCheck(writer2:PrintWriter) : String ={
    var leftType = left.typeCheck(writer2)
    var rightType = right.typeCheck(writer2)
    if(leftType == "INT" && rightType == "INT"){
      changeNodeColor(nodeNum, writer2, "/pastel13/3")
      leftType
    }
    else{
      changeNodeColor(nodeNum, writer2, "/pastel13/1")
      "BROKEN"
    }
   }
 }
  case class ASTSubtract(var nodeNum : String, left: Expression, right: Expression) extends Expression{
   override def print(parent : String, writer2 :PrintWriter){
     nodeNum=printParseTree1("-", parent , writer2,null) 
     left.print( nodeNum,writer2)
     right.print( nodeNum, writer2)
   }  
   override def typeCheck(writer2:PrintWriter) : String ={
    var leftType = left.typeCheck(writer2)
    var rightType = right.typeCheck(writer2)
    if(leftType == "INT" && rightType == "INT"){
      changeNodeColor(nodeNum, writer2, "/pastel13/3")
      leftType
    }
    else{
      changeNodeColor(nodeNum, writer2, "/pastel13/1")
      "BROKEN"
    }
   }
 }
  case class Identifier(var nodeNum : String, value : String) extends Expression{
    override def print(parent : String, writer2 :PrintWriter){
     nodeNum=printParseTree1(value, parent , writer2,null)
    }
    def printForType(parent : String, writer2 :PrintWriter):String={
      printParseTree1(value, parent , writer2,null)
    }
    override def typeCheck(writer2:PrintWriter) : String ={
     if(map.contains(value)){
       if(map(value)=="INT"){
        changeNodeColor(nodeNum, writer2, "/pastel13/3") 
       }
       else{
         changeNodeColor(nodeNum, writer2, "/pastel13/2")
       }
       map(value)
     }
     else{
       changeNodeColor(nodeNum, writer2, "/pastel13/1")
      "BROKEN" 
     }
   }
  }
  case class Number(var nodeNum : String, value : Integer) extends Expression{
    override def print(parent : String, writer2 :PrintWriter){
      nodeNum=printParseTree1(value.toString(), parent , writer2,null)
    }
    override def typeCheck(writer2:PrintWriter) : String ={
      changeNodeColor(nodeNum, writer2, "/pastel13/3")
     "INT"
   }
  }
  case class Boolliteral(var nodeNum : String, value : String) extends Expression{
    override def print(parent : String, writer2 :PrintWriter){
      nodeNum=printParseTree1(value, parent , writer2,null)
    }
   override def typeCheck(writer2:PrintWriter) : String ={
     changeNodeColor(nodeNum, writer2, "/pastel13/2")
     "BOOL"
   }
  } 
  case class ASTError(msg:String) extends RuntimeException( msg ) 
  case class ParseError(msg:String) extends RuntimeException( msg ) 
  case class ScannerError(msg:String) extends RuntimeException( msg ) 
  sealed abstract class NonTerminal(var counter: Integer)
  case object declarations extends NonTerminal(0)
  sealed abstract class Token(var value: String)
  case object LP extends Token("")
  case object RP extends Token("")
  case object ASGN extends Token("")
  case object SC extends Token("")
  case class MULTIPLICATIVE() extends Token("")
  case class ADDITIVE() extends Token("")
  case class COMPARE() extends Token("")
  case object IF extends Token("")
  case object THEN extends Token("")
  case object ELSE extends Token("")
  case object BEGIN extends Token("")
  case object END extends Token("")
  case object WHILE extends Token("")
  case object DO extends Token("")
  case object PROGRAM extends Token("")
  case object VAR extends Token("")
  case object AS extends Token("")
  case object INT extends Token("")
  case object BOOL extends Token("")
  case object WRITEINT extends Token("")
  case object READINT extends Token("")
  case class ident() extends Token("")
  case class boollit() extends Token("")
  case class num() extends Token("")
  var globalCounter = 1
  var map = scala.collection.mutable.HashMap.empty[String,String]
  def isExpr(tokens: List[Token], outfile: String, ASTFile:String): Boolean = {
    val writer = new PrintWriter(new File(outfile))
    var x = 0;
    var remaining = tokens
    def expr(): Start = remaining.headOption match {
      case Some(PROGRAM) => {
        var statementSequenceDecl = ListBuffer[ASTDeclarations]()
        var statementSequenceBody = ListBuffer[ASTStatement]()
        var parent = "n" + globalCounter
        writer.write("digraph parseTree {\n")
        writer.write("ordering=out;\n")
        writer.write("node [shape = box, style = filled];\n")
        var myId=printParseTree1("program",  null, writer,null)
        remaining = remaining.tail
        var epsilonId = printParseTreeEpsilon("PROGRAM", myId, parent, writer)
        statementSequenceDecl=declarations(myId, statementSequenceDecl)
        if (remaining.headOption != Some(BEGIN)) {
          throw ParseError("error in PROGRAM")
        }
       epsilonId = printParseTreeEpsilon("BEGIN", myId, parent, writer)
        remaining = remaining.tail
        var ptr = Start(null, statementSequenceDecl, statementSequence(myId, statementSequenceBody))
        if (remaining.headOption != Some(END)) {
          throw new ParseError("error in PROGRAM")
        }
       epsilonId = printParseTreeEpsilon("END", myId, parent, writer)
        remaining = remaining.tail
        writer.write("}\n")
        writer.close()
        ptr.print(ASTFile)
        ptr
      }
      case _ => {
        throw ParseError("error in PROGRAM")
      }
  }
def declarations(parent: String, st : ListBuffer[ASTDeclarations]): ListBuffer[ASTDeclarations] = remaining.headOption match {
      case Some(VAR) => {
        var label = "declarations"
        var eplabel = "VAR"
        var myId = printParseTree1(label , parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        if (remaining.headOption != Some(`ident`())) {
          throw ParseError("error in declarations")
        }
        //storing the variable name 
        var variableName = remaining.head.value
        eplabel ="ident: "+ remaining.head.value
        epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        var declIdent = Identifier(null, variableName)
        remaining = remaining.tail
        if (remaining.headOption != Some(AS)) {
          throw ParseError("error in declarations")
        }
        eplabel = "AS"
        epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        var declType=type1(myId, variableName)
        var newDecl = ASTdecl(null, declIdent, declType)
        st+=newDecl
        if (remaining.headOption != Some(SC)) {
          throw ParseError("error in declarations")
        }
        eplabel = ";"
        epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        declarations(myId, st)
      }
      case Some(BEGIN) => {
        var label = "declarations"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case _ => throw ParseError("Parse Error in declarations")
    }
    def type1(parent: String, variableName: String): Type = remaining.headOption match {
      case Some(INT) => {
        map += (variableName -> "INT")
        var label = "type1"
        var eplabel = "INT"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        ASTInt(null)
      }
      case Some(BOOL) => {
        map += (variableName -> "BOOL")
        var label = "type1"
        var eplabel = "BOOL"
        var myId = printParseTree1(label, parent, writer,null)
        myId = printParseTree1(label, parent, writer,null)
        remaining = remaining.tail
        ASTBool(null)
      }
      case _ => {
        throw ParseError("error in type1")
      }
    }
    def statementSequence(parent: String, st : ListBuffer[ASTStatement]): ListBuffer[ASTStatement] = remaining.headOption match {
      case Some(END) => {
        var label = "statementSequence"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case Some(ELSE) => {
        var label = "statementSequence"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case Some(IF) => {
        var label = "statementSequence"
        var eplabel = ";"
        var myId = printParseTree1(label, parent, writer,null)
        st += statement(myId)
        if (remaining.headOption != Some(SC)) {
          throw ParseError(remaining.head + "error in statementSequence1")
        }
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        statementSequence(myId, st)
      }
      case Some(WHILE) => {
        var label = "statementSequence"
        var eplabel = ";"
        var myId = printParseTree1(label, parent, writer,null)
        st += statement(myId)
        if (remaining.headOption != Some(SC)) {
          throw ParseError("error in parsing")
        }
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        statementSequence(myId, st)
      }
      case Some(WRITEINT) => {
        var label = "statementSequence"
        var eplabel = ";"
        var myId = printParseTree1(label, parent, writer,null)
        st += statement(myId)
        if (remaining.headOption != Some(SC)) {
          throw ParseError(remaining.head + "error in statementSequence3")
        }
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)  
        remaining = remaining.tail
        statementSequence(myId, st)
      }
      case Some(`ident`()) => {
        var label = "statementSequence"
        var eplabel = ";"
        var myId = printParseTree1(label, parent, writer,null)
        st += statement(myId)
        if (remaining.headOption != Some(SC)) {
          throw ParseError(remaining.head + "error in statementSequence4")
        }
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        statementSequence(myId, st)
      }
      case _ => {
        throw ParseError(remaining.head + "error in statementSequence5")
      }
    }
    def statement(parent: String): ASTStatement = remaining.headOption match {
      case Some(IF) => {
        var label = "statement"
        var myId = printParseTree1(label, parent, writer,null)
        ifStatement(myId)
      }
      case Some(WHILE) => {
        var label = "statement"
        var myId = printParseTree1(label, parent, writer,null)
        whileStatement(myId)
      }
      case Some(WRITEINT) => {
        var label = "statement"
        var myId = printParseTree1(label, parent, writer,null)
        writeInt(myId)
      }
      case Some(`ident`()) => {
        var label = "statement"
        var myId = printParseTree1(label, parent, writer,null)
        assignment(myId)
      }
      case _ => throw ParseError("Error parsing")
    }
    def assignment(parent: String): ASTStatement = remaining.headOption match {
      case Some(`ident`()) => {
        var label = "assignment"
        var eplabel = remaining.head.value
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        
        remaining = remaining.tail
        if (remaining.headOption != Some(ASGN)) {
          throw ParseError("Error parsing in assignment")
        }
        var eplabel2 = ":=" + remaining.head.value
        epsilonId=printParseTreeEpsilon(eplabel2, myId, parent, writer)
        
        remaining = remaining.tail
        assignmentA(myId, Identifier(null, eplabel))
      }
      case _ => {
        throw ParseError("error in assignment")
      }
    }
    def assignmentA(parent: String, st : Identifier): ASTStatement = remaining.headOption match {
      case Some(READINT) => {
        var label = "assignmentA"
        var eplabel = "READINT"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        ASTAssignReadInt(null, st)
        
      }
      case _ => {
        var label = "assignmentA"
        var myId = printParseTree1(label, parent, writer,null)
        ASTassignment(null, st, expression(myId))
      }
    }
    def ifStatement(parent: String): ASTStatement = remaining.headOption match {
      case Some(IF) => {
        var label = "ifStatement"
        var eplabel = "IF"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        var ifExpression = expression(myId)
        if (remaining.headOption != Some(THEN)) {
          throw ParseError("error in ifstatement")
        }
        eplabel = "THEN"
        epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)  
        remaining = remaining.tail
        var statementSequencest = ListBuffer[ASTStatement]()
        var ifStatementSequence = statementSequence(myId, statementSequencest)
        var statementSequencest2 = ListBuffer[ASTStatement]()
        var elseStatementSequence =elseClause(myId, statementSequencest2)
        if (remaining.headOption != Some(END)) {
          println("error in ifstatement")
          throw ParseError("parse error")
        }
        eplabel = "END"
        epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer) 
        remaining = remaining.tail
        ASTifStatement(null, ifExpression, ifStatementSequence, elseStatementSequence)
      }
      case _ => {
        println("error in ifStatement")
        throw ParseError("parse error")
      }
    }
    def elseClause(parent: String, st : ListBuffer[ASTStatement]): ListBuffer[ASTStatement] = remaining.headOption match {
      case Some(ELSE) => {
        var label = "elseClause"
        var eplabel = "ELSE"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)   
        remaining = remaining.tail
        statementSequence(myId,st)
      }
      case Some(END) => {
        var label = "elseClause"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        statementSequence(myId,st)
      }
      case _ => {
        println("error in elseClause")
        throw ParseError("parse error")
      }
    }
    def whileStatement(parent: String): ASTStatement = remaining.headOption match {
      case Some(WHILE) => {
        var label = "whileStatement"
        var eplabel = "WHILE"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        var whileExpression = expression(myId)
        if (remaining.headOption != Some(DO)) {
          println("error in whileStatement")
          throw ParseError("parse error")
        }
        eplabel = "DO"
        epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        var statementSequencest = ListBuffer[ASTStatement]()
        var ptr = ASTwhileStatement(null, whileExpression, statementSequence(myId, statementSequencest))
        if (remaining.headOption != Some(END)) {
          println("error in whilestatement")
          throw ParseError("parse error")
        }
        eplabel = "END"
        epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        ptr
      }
      case _ => throw ParseError("parse error")
    }
    def writeInt(parent: String): ASTStatement = remaining.headOption match {
      case Some(WRITEINT) => {
        var label = "writeInt"
        var eplabel = "WRITEINT"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        ASTwriteInt(null, expression(myId))
      }
      case _ => {
        println("error in writeInt")
        throw ParseError("parse error")
      }
    }
    def expression(parent: String): Expression = {
      var label = "expression"
      var myId = printParseTree1(label, parent, writer,null)
      expressionA(myId, simpleExpression(myId))
    }
    def expressionA(parent: String, st: Expression): Expression = remaining.headOption match {
      case Some(COMPARE()) => {
        var label = "expressionA"
        var eplabel = remaining.head.value
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        expressionA(myId,ASTCompare(null, eplabel, st, simpleExpression(myId)))
      }
      case Some(DO) => {
        var label = "expressionA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case Some(THEN) => {
        var label = "expressionA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case Some(SC) => {
        var label = "expressionA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case Some(RP) => {
        var label = "expressionA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case _ => {
        println("error in expressionA")
        throw ParseError("parse error")
      }
    }
    def simpleExpression(parent: String): Expression = {
      var label = "simpleExpression"
      var myId = printParseTree1(label, parent, writer,null)
      var st=term(myId)
      var ptr = simpleExpressionA(myId, st)
      ptr
    }
    def simpleExpressionA(parent: String, st : Expression): Expression = remaining.headOption match {
      case Some(ADDITIVE()) => {
        var label = "simpleExpressionA"
        var eplabel = remaining.head.value
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        remaining = remaining.tail
        var ptr=term(myId)
        var additiveNode = 
        eplabel match{
          case "+" =>{ASTAddition(null, st, ptr)}
          case _ =>{ ASTSubtract(null, st, ptr)}
        }
        var ptr2 = simpleExpressionA(myId, additiveNode)
        ptr2
      }
      case Some(COMPARE()) => {
        var label = "simpleExpressionA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case Some(DO) => {
        var label = "simpleExpressionA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case Some(THEN) => {
        var label = "simpleExpressionA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case Some(SC) => {
        var label = "simpleExpressionA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case Some(RP) => {
        var label = "simpleExpressionA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        st
      }
      case _ => {
        println("error in simpleExpression")
        throw ParseError("parse error")
      }
    }
    def term(parent : String): Expression = {
      var label = "term"
      var myId = printParseTree1(label, parent, writer,null)
      var st = factor(myId)
      termA(myId, st)
    }
    def termA(parent: String, st : Expression): Expression = remaining.headOption match {
      case Some(MULTIPLICATIVE()) => {
        var label = "termA"
        var eplabel = remaining.head.value
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)    
        remaining = remaining.tail
        var ptr = factor(myId)
        var multiplierNode = eplabel match{
          case "*" =>{ ASTMultiply(null, st, ptr)}
          case "div" =>{ ASTDivision(null, st, ptr)}
          case "mod" =>{ ASTMod(null, st, ptr)}
          case "_" =>{ 
            println("fixmenow")
            ASTDivision(null, st, ptr)
          }
        }
        var ptr2 = termA(myId, multiplierNode) 
        ptr2
      }
      case Some(ADDITIVE()) => {
        var label = "termA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        var ptr = st
        ptr
      }
      case Some(COMPARE()) => {
        var label = "termA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        var ptr = st
        ptr
      }
      case Some(DO) => {
        var label = "termA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        var ptr = st
        ptr
      }
      case Some(THEN) => {
        var label = "termA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        var ptr = st
        ptr
      }
      case Some(SC) => {
        var label = "termA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        var ptr = st
        ptr
      }
      case Some(RP) => {
        var label = "termA"
        var eplabel = "&#949;"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        var ptr = st
        ptr
      }
      case _ => {
        println("error in termA")
        throw ParseError("parse error")
      }
    }
    def factor(parent: String) : Expression = remaining.headOption match {
      case Some(`ident`()) => {
        var label = "factor"
        var eplabel = "ident: "+remaining.head.value
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        var identNode = Identifier(null, remaining.head.value)
        remaining = remaining.tail
        identNode
      }
      case Some(`num`()) => {
        var label = "factor"
        var eplabel = "num: "+remaining.head.value
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        var numNode = Number(null, Integer.valueOf(remaining.head.value))
        remaining = remaining.tail
        numNode
      }
      case Some(`boollit`()) => {
        var label = "factor"
        var eplabel = "boollit"+remaining.head.value
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(eplabel, myId, parent, writer)
        var boolNode = Boolliteral(null, remaining.head.value)
        remaining = remaining.tail
        boolNode
      }
      case Some(LP) => {
       var label = "factor"
       var eplabel = "LP"
        var myId = printParseTree1(label, parent, writer,null)
        var epsilonId=printParseTreeEpsilon(label, myId, parent, writer)
        remaining = remaining.tail
        var ptr = expression(myId)
        if (remaining.headOption != Some(RP)) {
          println("error in factor")
          throw new ParseError("parse error")
        }
        epsilonId=printParseTreeEpsilon(label, myId, parent, writer)
        remaining = remaining.tail
        ptr
      }
      case _ => {
        println("error in factor")
        throw new ParseError("parse error")
      }
    }
    try {
      globalCounter = 1
      expr()
      if (remaining.isEmpty) {
        true
      } else {
        false
      }
    } catch {
      case e: ParseError =>{
        println(e.getMessage)
        false
      } 
    }
  }
  def changeNodeColor(nodeNum:String, writer : PrintWriter, color :String){
    writer.write(nodeNum + " [fillcolor=\""+color+"\"]\n")
  }
  def printParseTree1(label : String, parent : String, writer : PrintWriter, color :String):String={
        var myId = "n" + globalCounter
        globalCounter = globalCounter + 1
        if (color == null){
          writer.write(myId + " [label=\""+label+"\",fillcolor=\"/x11/white\",shape=box]\n")
        }
        else{
           writer.write(myId + " [label=\""+label+"\",fillcolor=\""+color+"\",shape=box]\n")
        }
        if(parent != null){
          writer.write(parent + "->" + myId + "\n")
        }
        myId
  }
   def printParseTreeEpsilon(label: String, myId: String, parent : String, writer : PrintWriter):String={
        var epsilonId = "n" + globalCounter
        globalCounter = globalCounter + 1
        writer.write(epsilonId + " [label=\""+label+"\",fillcolor=\"/x11/white\",shape=box]\n")
        writer.write(myId + "->" + epsilonId + "\n")
        epsilonId
  }
  def main(argv: Array[String]) {
  if (argv.length == 0) {
      System.err.println("No file for input")
      sys.exit(0)
  }
    for (arg <- argv 
      if !arg.endsWith(".tl")) {
      System.err.println("Input file name, "+arg+", doesn't end with \".tl\"")
      sys.exit(1)
    }
   for (arg <- argv;
         fileNameStem = arg.replaceFirst(".tl$","")) {
      try {
        val sourceName = fileNameStem + ".tl"
        val parseTreeName = fileNameStem + ".pt.dot"
        val astName = fileNameStem + ".ast.dot"
        val ilocCFGName = fileNameStem + ".A3.cfg.dot"
        val mipsAsmName = fileNameStem + ".s"
        val source = Source.fromFile(sourceName)
        var lines = source.getLines
        val test = lines.map(line => line.split("\\s+").map(_.toString)).toList
        source.close
        cfgFile = ilocCFGName
        mipsFile = mipsAsmName
       var isComment = false;
      val buf = scala.collection.mutable.ListBuffer.empty[Token]
      val num1 = """([1-9][0-9]*|0)""".r
      val boollit1 = """(true|false)""".r
      val ident1 = """([A-Z][A-Z0-9]*)""".r
      val myReturn = """$""".r
      test.foreach(r => r.foreach(c => {
        if (isComment == false) {
          c.mkString("") match {
            case "%" =>{
              isComment = true;
            }
            case "var" =>{
              val info = new Info("var", VAR)
              buf += info.myType
            }
            case myReturn() =>{
              isComment = false;
            }
            case "=" | "!=" | "<" | ">" | "<=" | ">=" =>{
              object COMPARE1 extends COMPARE
              COMPARE1.value = c.mkString
              buf += COMPARE1
            }
            case "*" | "div" | "mod" =>{
              object MULTIPLICATIVE1 extends MULTIPLICATIVE
              MULTIPLICATIVE1.value = c.mkString
              buf += MULTIPLICATIVE1
            }
            case "(" =>{
              val info = new Info(c.mkString, LP)
              buf += info.myType
            }
            case ")" =>{
              val info = new Info(c.mkString, RP)
              buf += info.myType
            }
            case ":=" =>{
              val info = new Info(c.mkString, ASGN)
              buf += info.myType
            }
            case "end" =>{
              val info = new Info(c.mkString, END)
              buf += info.myType
            }
            case ";" =>{
              val info = new Info(c.mkString, SC)
              buf += info.myType
            }
            case "+" | "-" =>{
              object ADDITIVE1 extends ADDITIVE
              ADDITIVE1.value = c.mkString
              buf += ADDITIVE1
            }
            case "if" =>{
              val info = new Info(c.mkString, IF)
              buf += info.myType
            }
            case "then" =>{
              val info = new Info(c.mkString, THEN)
              buf += info.myType
            }
            case "else" =>{
              val info = new Info(c.mkString, ELSE)
              buf += info.myType
            }
            case "begin" =>{
              val info = new Info(c.mkString, BEGIN)
              buf += info.myType
            }
            case "while" =>{
              val info = new Info(c.mkString, WHILE)
              buf += info.myType
            }
            case "do" =>{
              val info = new Info(c.mkString, DO)
              buf += info.myType
            }
            case "program" =>{
              val info = new Info(c.mkString, PROGRAM)
              buf += info.myType
            }
            case "as" =>{
              val info = new Info(c.mkString, AS)
              buf += info.myType
            }
            case "int" =>{
              val info = new Info(c.mkString, INT)
              buf += info.myType
            }
            case "bool" =>{
              val info = new Info(c.mkString, BOOL)
              buf += info.myType
            }
            case "writeInt" =>{
              val info = new Info(c.mkString, WRITEINT)
              buf += info.myType
            }
            case "readInt" =>{
              val info = new Info(c.mkString, READINT)
              buf += info.myType
            }
            case boollit1(myBool) =>{
              object boollit2 extends boollit
              boollit2.value = c.mkString
              buf += boollit2
            }
            case ident1(myIdent) =>{
              object ident2 extends ident
              ident2.value = c.mkString
              buf += ident2
            }
            case num1(myNum) =>{
              object num2 extends num
              num2.value = c.mkString
              buf += num2
            }
            case _ =>{
              throw new ScannerError("The specified expression is not in the language")
            }
          }
        } else {
          c.mkString("") match {
            case myReturn() =>
              isComment = false;
            case _ =>
          }
        }
      }))
      val buf2: scala.collection.immutable.List[Token] = buf.toList
      println(s"[$fileNameStem.t1]: ",isExpr(buf2, parseTreeName, astName))
      }catch{
        case e: ScannerError => {
          print(s"Error processing [$fileNameStem.t1]: ")
          println(e.getMessage)
        }
      }
   }
  }
  class Info(var actualValue: String, var myType: Token) {
  }
}