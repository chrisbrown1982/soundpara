module Lang 

import Data.Nat

%default total

data AExp : Type where 
    ANum  : (n : Nat) -> AExp 
    AVar  : (x : Nat) -> AExp 
    APlus : (a1 : AExp) -> (a2 : AExp) -> AExp 
    AMin  : (a1 : AExp) -> (a2 : AExp) -> AExp 
    AMul  : (a1 : AExp) -> (a2 : AExp) -> AExp 

{------------------------------------
Evaluation of arithmetic expressions
-------------------------------------}
data AEvalRel : (AExp, List Nat) -> (n : Nat) -> Type where 
    MkEvalNum : AEvalRel (ANum n,s) n
    -- MkEvalLoc
    MkEvalSum : AEvalRel (a0,s) n0
             -> AEvalRel (a1,s) n1
             -> AEvalRel ((APlus a0 a1), s) n
    MkEvalSub : AEvalRel (a0,s) n0
             -> AEvalRel (a1,s) n1
             -> AEvalRel ((AMin a0 a1), s) n
    MkEvalProd : AEvalRel (a0,s) n0
              -> AEvalRel (a1,s) n1
              -> AEvalRel ((AMul a0 a1), s) n

{-----------------------------------
Boolean expressions
------------------------------------}

data BExp : Type where 
    BTrue  : BExp 
    BFalse : BExp 
    BEq    : (a1 : AExp) -> (a2 : AExp) -> BExp 
    BLTE   : (a1 : AExp) -> (a2 : AExp) -> BExp 
    BNot   : (b1 : BExp) -> BExp 
    BAnd   : (b1 : BExp) -> (b2 : BExp) -> BExp 
    BOr    : (b1 : BExp) -> (b2 : BExp) -> BExp 

{-----------------------------------
Evaluation of Boolean expressions
------------------------------------}

data BEvalRel : (BExp, List Nat) -> BExp -> Type where 
    MkEvalTrue  : BEvalRel (BTrue, s) BTrue 
    MkEvalFalse : BEvalRel (BFalse, s) BFalse 
    MkEvalEq1 : AEvalRel (a0,s) n
             -> AEvalRel (a1,s) m 
             -> (n = m)
             -> BEvalRel ((BEq a0 a0),s) BTrue
    MkEvalEq2 : AEvalRel (a0,s) n 
             -> AEvalRel (a1,s) m
             -> Not (n = m) 
             -> BEvalRel ((BEq a0 a1),s) BFalse
    MkEvalLte1 : AEvalRel (a0,s) n
             -> AEvalRel (a1,s) m 
             -> (LTE n m)
             -> BEvalRel ((BEq a0 a0),s) BTrue
    MkEvalLte2 : AEvalRel (a0,s) n
             -> AEvalRel (a1,s) m 
             -> Not (LTE n m)
             -> BEvalRel ((BEq a0 a0),s) BFalse
    MkEvalNot1 : BEvalRel (b,s) BTrue  
              -> BEvalRel (BNot b, s) BFalse 
    MkEvalNot2 : BEvalRel (b,s) BFalse 
              -> BEvalRel (BNot b, s) BTrue
    MkEvalAnd1 : BEvalRel (b0,s) BTrue
              -> BEvalRel (b1,s) BTrue 
              -> BEvalRel (BAnd b0 b1,s) BTrue 
    MkEvalAnd2 : BEvalRel (b0,s) BFalse
              -> BEvalRel (b1,s) BTrue 
              -> BEvalRel (BAnd b0 b1,s) BFalse
    MkEvalAnd3 : BEvalRel (b0,s) BTrue
              -> BEvalRel (b1,s) BFalse 
              -> BEvalRel (BAnd b0 b1,s) BFalse
    MkEvalOr1 : BEvalRel (b0,s) BTrue
              -> BEvalRel (b1,s) n 
              -> BEvalRel (BAnd b0 b1,s) BTrue 
    MkEvalOr2 : BEvalRel (b0,s) n
              -> BEvalRel (b1,s) BTrue 
              -> BEvalRel (BAnd b0 b1,s) BTrue
    MkEvalOr3 : BEvalRel (b0,s) BFalse
              -> BEvalRel (b1,s) BFalse 
              -> BEvalRel (BAnd b0 b1,s) BFalse 

data Com : Type where 
    CSkip   : Com 
    CAssign : (x : Nat) -> (a : AExp) -> Com 
    CStmt   : (c0, c1 : Com) -> Com 
    CIf     : (b : BExp) -> (c0 : Com) -> (c1 : Com) -> Com 
    CWhile  : (b : BExp) -> (c  : Com) -> Com 