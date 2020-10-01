module HW5 where

import Prelude hiding (LT, GT, EQ)
import System.IO
import Base
import Data.Maybe
import Data.List
import Operators
import RecursiveFunctionsAST
import RecursiveFunctionsParse


{-
What to submit (via Blackboard): a single file, named
HW5_pawprint.hs, where pawprint is your MU username. The file should
contain definitions for every function listed below. Furthermore,
everyone should adhere to the following guidelines to get full credit:

* Rename the given file HW5.hs to HW5_pawprint.hs. Only turn in HW5_pawprint.hs!

* Your submission must successfully load and typecheck in Haskell Platform to
get any points. For example, executing:
     $ ghci HW5_pawprint.hs
should not produce any errors. We won't attempt to grade assignments that fail to load.

* Name all functions and data types exactly as they appear in the
assignment. Grading will be partly automated, so incorrectly named functions are
likely to be counted as undefined functions.

* The code you submit must be your own. Exceptions: you may (of course) use
the code we provide however you like, including examples from the slides.

* No late submissions---PLEASE START EARLY!

-}

{-
For each of the following questions, put your answer directly below the 
question. This homework is due on Friday, November 18th, by 3pm.

(1) You must use a text editor (e.g., vi, textpad, emacs, etc.) to prepare 
    your solution. 
(2) You must write type declarations for each and every one of your Haskell
    definitions.
(3) The program you turn in must be the product of your effort alone.
(4) You may *not* import any Haskell library without the expressed permission
    of Professor Harrison. In other words, do not add any import declarations at
    the top of this file.
-}


--
-- The parsing function, parseExp :: String -> Exp, is defined for you.
--

facvar = parseExp ("var fac = function(n) { if (n==0) 1 else n * fac(n-1) };" ++
                   "fac(5)")

facrec = parseExp ("rec fac = function(n) { if (n==0) 1 else n * fac(n-1) };" ++
                   "fac(5)")

e1     = parseExp "var a = 3; var b = 8; var a = b, b = a; a + b"
e2     = parseExp "var a = 3; var b = 8; var a = b; var b = a; a + b"
e3     = parseExp "var a = 2, b = 7; (var m = 5 * a, n = b - 1; a * n + b / m) + a"
e4     = parseExp "var a = 2, b = 7; (var m = 5 * a, n = m - 1; a * n + b / m) + a"         
-- N.b.,                                                ^^^ is a free occurence of m


{- Problem 1. Multiple declarations.

Notice first that the syntax of local declarations has changed (in RecursiveFunctionsAST.hs):
data Exp = ...
         | Declare    [(String,Exp)] Exp
           ...

Now, a declaration can take multiple bindings, so it will generally have the form:
   Declare [(x1,e1),...,(xn,en)] body

A call to the evaluation function, evaluation (Declare [(x1,e1),...,(xn,en)] body) env, should
process these declarations in the following way:
1. Evaluate each of e1,...,en in the environment env, producing values v1,...,vn;
2. Make a new environment adding bindings [(x1,v1),...,(xn,vn)] to env;
3. Evaluate body in this new environment.

Extend the definition of evaluate below to accommodate the multiple bindings. You can then
test your answer on the expressions, e1,...,e4, defined above. Note that e4 has a free occurrence
of m and, so, it should crash. You can also come up with your own test cases.
-}


-----------------
-- The evaluation function for the recursive function language.
-----------------

evaluate :: Exp -> Env -> Value
evaluate (Literal v) env = v

evaluate (Unary op a) env = 
  unary op (evaluate a env)

evaluate (Binary op a b) env = 
  binary op (evaluate a env) (evaluate b env)

evaluate (If a b c) env = 
  let BoolV test = evaluate a env in
    if test then evaluate b env
            else evaluate c env

evaluate (Variable x) env = fromJust x (lookup x env)
  where fromJust x (Just v) = v
        fromJust x Nothing  = error ("Variable " ++ x ++ " unbound!")

evaluate (Function x body) env = ClosureV x body env

evaluate (Declare list body) env = evaluate body newEnv
  where (xs, es) = unzip list 
        newEnv  = zip xs ([ evaluate e env | e <- es ]) ++ env

evaluate (RecDeclare x exp body) env = evaluate body newEnv
  where newEnv = (x, evaluate exp newEnv) : env

evaluate (Call fun arg) env = evaluate body newEnv
  where ClosureV x body closeEnv = evaluate fun env
        newEnv = (x, evaluate arg env) : closeEnv

execute exp = evaluate exp []


{- 2. Free variables. 

Recall from the LanguageSyntax.ppt slides that a variable occurrence in an expression is free if it
does not occur within the scope of a declaration of that variable.

Consider the following example written in concrete syntax:
     var m = 5, n = m; n + m
                    ^1 ^2  ^3
This has three variable occurrences, labelled 1, 2, and 3. Occurrences 2 and 3 are bound by the
declarations n = m and m = 5, respectively.

Depending on how the scope rules we pick, occurrence 1 could be either free or bound.
Consider an declaration expression of the form, "var x1=e1,...,xn=en ; body".

Scope Rule 1. The scope of each declaration, x1=e1,...,xn=en, consists only of body. In particular,
the scope of the declarations of xi=ei does *not* include the e1,...,en. By this rule, occurrence 1
above is free, because it is not within the scope of m=5.

Scope Rule 2. The scope of declaration xi=ei includes e_i+1,...,en and body. So, given the declaration
x1=e1, x1 does not occur free in e2,...,en or body. With this rule, occurrence 1 is bound by
the declaration m=5.

Problem 2.

Write a function, free :: [String] -> Exp -> [String], that finds the free occurrences of an expression
according to Scope Rule 1. In particular, (free seen e) should be the free occurrences of
variables in e that do not occur in the seen list.

The cases that are most important to think through are the cases where variable declarations
occur: Declare, RecDeclare, and Function.

Hint: it may help to remember that:
   map :: (a -> b) -> [a] -> [b]
   concat :: [[a]] -> [a]
when doing the Declare case.

-}

free :: [String] -> Exp -> [String]
free seen (Literal _ ) = []
free seen (Unary _ e) = free seen e
free seen (Binary _ x y) = free seen x ++ free seen y
free seen (If a b c) = free seen a ++ free seen b ++ free seen c
free seen (Variable x) = if elem x seen then [] else [x]
free seen (Function x e) = free (x:seen) e
free seen (Declare list body) = (findexp list) ++ (free (newseen list) body)
        where newseen [] = seen
              newseen ((x,exp):xs) = x:newseen xs
              findexp [] = []
              findexp ((x,exp):xs) = (free seen exp) ++ findexp xs 
free seen (RecDeclare x exp body) = free (x:seen) exp ++ free (x:seen) body
free seen (Call fun arg) = free seen fun ++ free seen arg


{-
Read-Eval-Print Loop.

Below is code for a simple REPL (read-eval-print-loop). Go ahead and try it out. You can
type in expressions, they are evaluated, the value is printed, and the loop starts over.
you can quit by typing "quit" at the prompt.

Problem 3.

Add checking for undefined (i.e., free variables) to the REPL. Change the program so that
it checks for free variables first using your answer from problem 2, and then, if there
are free variables, prints out an error message rather than evaluating the input.

As-is the REPL behaves like this:
-- RecFun> var x=9; x + 8
-- IntV 17
--
-- RecFun> x + 8
-- *** Exception: Variable x unbound!

Your solution should behave as:
-- RecFun> var x=9; x + 8
-- IntV 17
--
-- RecFun> x + 8
-- Unbound Variables: ["x"]
-- RecFun>

Note that, after finding an unbound variable, the REPL continues, so don't fail using the error
function.
-}

repl :: IO ()
repl = do
         putStr "RecFun> "
         iline <- getLine
         process iline

process :: String -> IO ()
process "quit" = return ()
process iline  = do
  if free [] e == [] then putStrLn (show v ++ "\n") else putStrLn ("Unbound Variable: " ++ show (free [] e) ++"\n")
  repl
   where e = parseExp iline
         v = evaluate e []




