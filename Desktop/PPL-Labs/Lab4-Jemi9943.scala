package jsy.student

object Lab4 extends jsy.util.JsyApplication {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * Jennifer Michael
   * 
   * Partner: Jessica Petty and Taylor Thomas
   * Collaborators: Cameron Taylor, Jace Conflenti
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => {return l}
    case first :: (t1 @ (rest :: _)) => {    //List begins with first, second is second, and firstSecond is list beginning
      var compList = compressRec(t1)          //with second and ending with _
      if(first == rest) return compList     //firstSecond is new list with second at head. recurse remainder of list
      else return first :: compList          //if first==second, return the remainder, otherwise join second with compressed list
    }
  }

  //same as compressRec but from the other side
  //h is the last element of the list
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match{
        //first iteration, acc is empty, and we append acc to h
        //if acc has something, and there's a repeat, return acc
        //otherwise append h to the acc
      case h1 :: _ => if (h==h1) acc else h :: acc
      case Nil | _ :: Nil => h::acc
    }
  }

  //finds first element in l which, after f is applied, returns some(x)
  def mapFirst[A](f: A => Option[A])(l: List[A]): List[A] = l match {
    case Nil => Nil
    case h :: t => f(h) match {
      case Some(a) => a :: t
      case _ => h :: mapFirst(f)(t)
    }
  }
  
  /* Search Trees */
  
  sealed abstract class Tree {
    def insert(n: Int): Tree = this match {
      case Empty => Node(Empty, n, Empty)
      case Node(l, d, r) => if (n < d) Node(l insert n, d, r) else Node(l, d, r insert n)
    } 

    /* Fold left takes something of type A and function that takes something of
    type A and returns type A. With loop, it takes a tree. For sum, the original z/acc
    value is 0. When you get to a leaf, you add acc (first, 0) to the data value. Now
    acc is really  accumulating. The rest is just traversing the tree by going down subtrees
    and adding the data value to whatever the accumulator is.
     */
    def foldLeft[A](z: A)(f: (A, Int) => A): A = {
      def loop(acc: A, t: Tree): A = t match {
          //if node is terminal, return accumulators
        case Empty => acc
          //otherwise do an in-order traversal
        case Node(l, d, r) => {
          //recurse left subtree
          var left = loop(acc, l)
          //apply function to data value
          var data = f(left, d)
          //recurse the right and return
          loop(data, r)

        }
      }
      loop(z, this)
    }
    
    def pretty: String = {
      def p(acc: String, t: Tree, indent: Int): String = t match {
        case Empty => acc
        case Node(l, d, r) =>
          val spacer = " " * indent
          p("%s%d%n".format(spacer, d) + p(acc, l, indent + 2), r, indent + 2)
      } 
      p("", this, 0)
    }
  }
  case object Empty extends Tree
  case class Node(l: Tree, d: Int, r: Tree) extends Tree
  
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }
  
  def sum(t: Tree): Int = t.foldLeft(0){ (acc, d) => acc + d }
  
  def strictlyOrdered(t: Tree): Boolean = {
    /*Okay. So we run foldLeft on the tree, the type A we give it is a tuple(Bool, Option)
    The function f we're giving it is the case statements below.
    The first case is if we're at a terminal node (None). Then we propogate up
    the boolean.
    The second case is if we're not at a terminal node. If the tree is still valid,
    we keep going. If its not, we change value to false, which will propogate up.
    After the function f is applied to every node in the tree (all elements),
    we only care about the boolean value, not the optional int.
    We return that int.
     */
    val (b, _) = t.foldLeft((true, None: Option[Int])){
      case ((bol, None), d) => (bol, Some(d))
      case ((bol, Some(i)), d) => if (i < d) (bol, Some(d)) else (false, Some(d))
    }
    b
  }


  /* Type Inference */

  type TEnv = Map[String, Typ]
  val emp: TEnv = Map()
  def get(env: TEnv, x: String): Typ = env(x)
  def extend(env: TEnv, x: String, t: Typ): TEnv = env + (x -> t)

  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def typeInfer(env: TEnv, e: Expr): Typ = {
    // Some shortcuts for convenience
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => env(x)
      case ConstDecl(x, e1, e2) => typeInfer(extend(env, x, typ(e1)), e2)
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typ(e1), typ(e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (TNumber,tgot) => err(tgot, e2)
        case (TString, tgot) => err(tgot, e2)
        case (_,_) => err(typ(e1), e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typ(e1), typ(e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TNumber, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1)
      }
      case Binary(Eq|Ne, e1, e2) => (typ(e1), typ(e2)) match {
        case (TFunction(_,_), _) => err(typ(e1), e1)
        case (typ1, typ2) => if (typ1 == typ2) TBool else err(typ(e2), e2)
        case (_, _) => err(typ(e1), e1)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typ(e1), typ(e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (TNumber, tgot) => err(tgot, e2)
        case (TString, tgot) => err(tgot, e2)
        case (_, _) => err(typ(e1), e1)
      }
      case Binary(And|Or, e1, e2) => (typ(e1), typ(e2)) match {
        case (TBool, TBool) => TBool
        case (TBool, tgot) => err(tgot, e2)
        case (_, _) => err(typ(e1), e1)
      }
      case Binary(Seq, e1, e2) => typ(e1); typ(e2)

      case If(e1, e2, e3) => typ(e1) match {
        case TBool => (typ(e2), typ(e3)) match {
          case(typ1, typ2) => if (typ1 == typ2) typ1 else err(typ2, e3)
          case (_, _) => err(typ(e2), e2)
        }
        case _ => err(typ(e1), e1)
      }
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            extend(env, f, tprime)
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = env1 ++ params
        // Match on whether the return type is specified.
        tann match {
          case None => TFunction(params, typeInfer(env2, e1))
          case Some(tret) => {
            val t = typeInfer(env2, e1)
            if (t == tret) TFunction(params, tret) else err(t, e1)
          }
        }
      }
      case Call(e1, args) => typ(e1) match {
        case TFunction(params, tret) if params.length == args.length =>
          (params, args).zipped.foreach {
            (param, arg) => (param, arg) match {
              case ((pString, pType), aExp) => if (pType != typeInfer(env, aExp)) err(typeInfer(env, aExp), aExp)
            }
          };
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.map{case (x,y) => (x, typ(y))})
      case GetField(e1, f) => typ(e1) match {
        case TObj(fields) => if (fields.contains(f)) fields(f) else err(typ(e1), e1)
        case _ => err(typ(e1), e1)
      }
    }
  }


  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), "v1 in inequalityVal is not a value")
    require(isValue(v2), "v2 in inqualityVal is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => (bop: @unchecked) match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case (N(n1), N(n2)) => (bop: @unchecked) match {
        case Lt => n1 < n2
        case Le => n1 <= n2
        case Gt => n1 > n2
        case Ge => n1 >= n2
      }
      case _ => throw StuckError(Binary(bop, v1, v2))
    }
  }

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v), "Expr to substitute is not a value")

    def subst(e: Expr): Expr = substitute(e, v, x)

    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
      /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) v else e
      case ConstDecl(y, e1, e2) => if (y == x) ConstDecl(y, subst(e1), e2) else ConstDecl(y, subst(e1), subst(e2))
      /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => {
        if (params.foldLeft(false)( (bool, param) => (param._1 == x) || bool) ||  Some(x) == p) e
        else Function(p, params, tann, subst(e1))
      }
      case Call(e1, args) => Call(subst(e1), args.map(arg => subst(arg)))
      /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.map(field => (field._1, subst(field._2))))
      case GetField(e1, f) => if (f != x) GetField(subst(e1), f) else e
    }
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), "input Expr to step is a value")

    def stepIfNotValue(e: Expr): Option[Expr] = if (isValue(e)) None else Some(step(e))

    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

      case Unary(Neg, N(n1)) => N(-n1)
      case Unary(Not, B(b1)) => B(!b1)
      case Unary(uop, v1) if isValue(v1) => throw StuckError(e)

      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)
      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => throw StuckError(e)

      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Div, N(n1), N(n2)) => N(n1 / n2)
      case Binary(Times, v1, v2) if isValue(v1) && isValue(v2) => throw StuckError(e)
      case Binary(Minus, v1, v2) if isValue(v1) && isValue(v2) => throw StuckError(e)
      case Binary(Div, v1, v2) if isValue(v1) && isValue(v2) => throw StuckError(e)

      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1, v2))
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)

      case Binary(And, B(true), e2) => e2
      case Binary(And, B(false), e2) => B(false)
      case Binary(Or, B(true), e2) => B(true)
      case Binary(Or, B(false), e2) => e2
      case Binary(And, v1, e2) if isValue(v1) => throw StuckError(e)
      case Binary(Or, v1, e2) if isValue(v1) => throw StuckError(e)

      case If(B(true), e2, e3) => e2
      case If(B(false), e2, e3) => e3
      case If(v1, e2, e3) if isValue(v1) => throw StuckError(e)

      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)

      case Call(v1, args) if isValue(v1) && (args forall isValue) =>
        v1 match {
          case Function(p, params, _, e1) => {
            // Each paramater is (name: String, type: Type), so returns tuple of (param, arg) with e1p
            val e1p = (params, args).zipped.foldRight(e1){
              case ((x, v), e1pp) => substitute(e1pp, v, x._1)
            }
            p match {
              case None => e1p
              case Some(x1) => substitute(e1p, v1, x1)
            }
          }
          case _ => throw StuckError(e)
        }

      case GetField(Obj(fields), f) => fields.get(f) match {
        case Some(x) => x
        case None => throw StuckError(e)
      }
      case GetField(v1, f) if isValue(v1) => throw StuckError(e)

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

      case Unary(uop, e1) => Unary(uop, step(e1))

      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)

      case If(e1, e2, e3) => If(step(e1), e2, e3)

      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)

      case Call(v1 @ Function(_, _, _, _), args) => Call(v1, mapFirst(stepIfNotValue)(args))
      case Call(e1, args) => Call(step(e1), args)

      case Obj(fields) => {
        val fieldMap: Map[String, Expr] = Map()
        val newObj = fields.foldLeft((true,fieldMap)) {
          (ret, field) =>
            if (ret._1) {
              if (isValue(field._2)) (ret._1, ret._2 + (field._1 -> field._2)) else (false, ret._2 + (field._1 -> step(field._2)))
            } else (ret._1, ret._2 + (field._1 -> field._2))
        }
        Obj(newObj._2)
      }
      case GetField(e1, f) => GetField(step(e1), f)


      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }


  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information

  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  def iterateStep(e: Expr): Expr = {
    require(closed(e), "input Expr to interateStep is not closed")
    def loop(e: Expr, n: Int): Expr = {
      if (debug) { println("Step %s: %s".format(n, e)) }
      if (isValue(e)) e else loop(step(e), n + 1)
    }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val v = loop(e, 0)
    if (debug) {
      println("Value: " + v)
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(Parser.parse(s))

  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val e1 =
      handle(None: Option[Expr]) {Some{
        Parser.parseFile(file)
      }} getOrElse {
        return
      }

    val welltyped = handle(false) {
      println("# Type checking ...")
      val t = Lab4.inferType(e1)
      println(pretty(t))
      true
    }
    if (!welltyped) return

    handle() {
      println("# Stepping ...")
      def loop(e: Expr, n: Int): Expr = {
        println("## %4d: %s".format(n, e))
        if (isValue(e)) e else loop(Lab4.step(e), n + 1)
      }
      val v1 = loop(e1, 0)
      println(pretty(v1))
    }
  }

}

