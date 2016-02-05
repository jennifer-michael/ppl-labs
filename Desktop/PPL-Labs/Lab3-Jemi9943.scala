package jsy.student

object Lab3 extends jsy.util.JsyApplication {
  import jsy.lab3.Parser
  import jsy.lab3.ast._

  /*
   * CSCI 3155: Lab 3 
   * Jennifer Michael
   * 
   * Partner: Cameron Taylor
   * Collaborators: Steven Conflenti, Jessica Petty
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
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }

  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => try s.toDouble catch {case _: Throwable => Double.NaN}
      case Function(_, _, _) => Double.NaN
      case _ => throw new UnsupportedOperationException
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => if(n == 0 || n.isNaN ) false else true
      case Undefined => false
      case S(s) => if(s == "") false else true
      case Function(_, _, _) => true
      case _ => throw new UnsupportedOperationException
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString
      case B(true) => "true"
      case B(false) => "false"
      case Undefined => "undefined"
      case S(s) => s
      // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
      // of the function (from the input program).
      case Function(_, _, _) => "function"

    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case _ =>
        val (n1, n2) = (toNumber(v1), toNumber(v2))
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */

  /*
   * This code is a reference implementation of JavaScripty without
   * strings and functions (i.e., Lab 2).  You are to welcome to
   * replace it with your code from Lab 2.
   */
  def eval(env: Env, e: Expr): Expr = {
    def eToN(e: Expr): Double = toNumber(eval(env, e))
    def eToB(e: Expr): Boolean = toBoolean(eval(env, e))
    def eToVal(e: Expr): Expr = eval(env, e)
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => get(env, x)

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      // ****** Your cases here
      case Unary(uop, e1) => uop match {
        case Neg => N(-eToN(e1))
        case Not => B(!eToB(e1))
      }

      case Binary(bop, e1, e2) => bop match {

        case Plus => (eToVal(e1), eToVal(e2)) match {
          case (S(s1), v2) => S(s1 + toStr(v2))
          case (v1, S(s2)) => S(toStr(v1) + s2)
          case (v1, v2) => N(toNumber(v1) + toNumber(v2))
        }
        case Minus => N(eToN(e1) - eToN(e2))
        case Times => N(eToN(e1) * eToN(e2))
        case Div => N(eToN(e1) / eToN(e2))

        case Eq => (e1, e2) match {
          case (_, Function(_,_,_)) => throw new DynamicTypeError(e)
          case (Function(_,_,_), _) => throw new DynamicTypeError(e)
          case (_,_) => B(eToVal(e1) == eToVal(e2))
        }
        case Ne => (e1, e2) match {
          case (_, Function(_,_,_)) => throw new DynamicTypeError(e)
          case (Function(_,_,_), _) => throw new DynamicTypeError(e)
          case (_,_) => B(eToVal(e1) != eToVal(e2))
        }

        case Lt|Le|Gt|Ge => B(inequalityVal(bop, eToVal(e1), eToVal(e2)))

        case And =>
          val v1 = eToVal(e1)
          if(toBoolean(v1)) eToVal(e2) else v1
        case Or =>
          val v1 = eToVal(e1)
          if(toBoolean(v1)) v1 else eToVal(e2)

        case Seq => eToVal(e1); eToVal(e2)

      }
      case If(e1, e2, e3) => if(eToB(e1)) eToVal(e2) else eToVal(e3)

      case ConstDecl(x, e1, e2) => eval(extend(env, x, eToVal(e1)), e2)

      case Call(e1, e2) => val v1 = eToVal(e1)
        v1 match {
          case Function(None, x, b) =>
            val env2 = extend(env, x, eToVal(e2))
            eval(env2, b)

          case Function(Some(p), x, b) =>
            val env2 = extend(env, p, eToVal(e1))
            val env3 = extend(env2, x, eToVal(e2))
            eval(env3, b)

          case _ => throw new DynamicTypeError(e)
        }

      case _ => throw new UnsupportedOperationException
    }
  }


  /* Small-Step Interpreter with Static Scoping */

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    def subst(e: Expr): Expr = substitute(e, v, x)
    /* Body */
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))

      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))

      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      //case If(e1, e2, e3) => if(toBoolean(subst(e1))) subst(e2) else subst(e3)

      case Var(str) => if(str == x) v else Var(str)

      case ConstDecl(str, e1, e2) => if(str == x) ConstDecl(str, subst(e1), e2)
      else ConstDecl(str, subst(e1), subst(e2))

      case Call(e1, e2) => Call(subst(e1), subst(e2))

      case Function(p, y, e1) => p match {
          //Case if value we want to substitute is the same as either the name or parameter passed
          //Else run subst on the body of the function
        case Some(z) => if (z == x || y == x) e else Function(p, y, subst(e1))
          //Case if function is not recursable
        case None => if (y == x) e else Function(None, y, subst(e1))
      }

      case _ => throw new IllegalArgumentException
    }
  }

  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

      // ****** Your cases here

        //DoNeg
      case Unary(Neg, v1) if isValue(v1) => N(-toNumber(v1))
        //DoNot
      case Unary(Not, v1) if isValue(v1) => B(!toBoolean(v1))

        //DoSeq
      case Binary(Seq, v1, e1) if isValue(v1) => e1
        //DoAndTrue and DoAndFalse: short-circuiting if false
      case Binary(And, v1, e1) if isValue(v1) => if(toBoolean(v1)) e1 else v1
        //DoOrTrue and DoOrFalse: short-circuiting if true
      case Binary(Or, v1, e1) if isValue(v1) => if(toBoolean(v1)) v1 else e1
        //Base case if e1 and e2 are now values:
      case Binary(bop, v1, v2) if isValue(v1) && isValue(v2) => (bop: @unchecked) match {
        case Plus => (v1, v2) match {
            //DoPlusString1
          case (S(s1), v2) => S(s1 + toStr(v2))
            //DoPlusString2
          case (v1, S(s2)) => S(toStr(v1) + s2)
            //DoPlusNumber
          case (_, _) => N(toNumber(v1) + toNumber(v2))
        }
          //DoArith
        case Minus => N(toNumber(v1) - toNumber(v2))
        case Times => N(toNumber(v1) * toNumber(v2))
        case Div => N(toNumber(v1) / toNumber(v2))

          //DoEquality
        case Eq => (v1, v2) match {
            //First 2 premises
          case (Function(_, _, _), _) | (_, Function(_, _, _)) => throw new DynamicTypeError(e)
          case(_, _) => B(v1 == v2)
        }
          //Disequality
        case Ne => (v1, v2) match {
          case (Function(_, _, _), _) | (_, Function(_, _, _)) => throw new DynamicTypeError(e)
          case(_, _) => B(v1 != v2)
        }
          //DoInequality Rules
        case (bop2 @ (Lt | Le | Gt | Ge)) => B(inequalityVal(bop2, v1, v2))
      }

        //DoIfTrue and DoIfFalse
      case If(v1, e2, e3) if isValue(v1) => if(toBoolean(v1)) e2 else e3

        //DoConst. e2[v1/x] means substitute
      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)

        //DoCall and DoCallRec (with substitutes)
      case Call(v1, v2) if isValue(v1) && isValue(v2) => v1 match {
          //DoCallRec
        case Function(Some(p), x, b) => substitute(substitute(b, v1, p), v2, x)
          //DoCall
        case Function(None, x, b) => substitute(b, v2, x)
        case _ => throw new DynamicTypeError(e)
      }

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

      // ****** Your cases here

        //SearchUnary
      case Unary(uop, e1) => Unary(uop, step(e1))

        //SearchBinaryArith
      case Binary(bop, v1, e2) if isValue(v1)  => Binary(bop, v1, step(e2))
        //SearchBinary
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)

        //SearchIf
      case If(e1, e2, e3) => If(step(e1), e2, e3)

        //SearchConst
      case ConstDecl(x, v1, e2) if isValue(v1) => ConstDecl(x, v1, step(e2))
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)

        //SearchCall2
      case Call(v1, e2) if isValue(v1) => Call(v1, step(e2))
        //SearchCall1
      case Call(e1, e2) => Call(step(e1), e2)

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information

  // Interface to run your big-step interpreter starting from an empty environment and print out
  // the test input if debugging.
  def evaluate(e: Expr): Expr = {
    require(closed(e))
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with eval ...")
      println("\nExpression:\n  " + e)
    }
    val v = eval(emp, e)
    if (debug) {
      println("Value: " + v)
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def evaluate(s: String): Expr = evaluate(Parser.parse(s))

  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  def iterateStep(e: Expr): Expr = {
    require(closed(e))
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

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }

    val expr =
      handle(None: Option[Expr]) {Some{
        Parser.parseFile(file)
      }} getOrElse {
        return
      }

    handle() {
      val v1 = iterateStep(expr)
      println(pretty(v1))
    }
  }

}