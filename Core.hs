module Core where

import Data.Set(Set, singleton, delete, insert, map, empty, elemAt, toList, member)
import Data.List(nub,sort)
import Control.Monad(when,forM_)
import StateMonad


-- Kripke structure states are ints.
type State = Int

{-
    KS (n, l, r), where 'n' indicates the states [0 .. n], 'l' is the labeling function,
    and 'r' is the transition relation.
-}
data KripkeS = KS (Int, State->[State], State->(At->Bool))


-- Propositional vars are strings.
type At = String

-- State forms.
data StateF = Var At
            | Neg At
            | ConjS StateF StateF
            | DisyS StateF StateF
            | A PathF
            | E PathF deriving (Eq, Ord)

-- Path forms.
data PathF = St StateF
           | DisyP PathF PathF
           | ConjP PathF PathF
           | U PathF PathF
           | V PathF PathF
           | X PathF deriving (Eq,Ord)


negS::StateF->StateF
negS φ = case φ of
          Var a -> Neg a
          Neg a -> Var a 
          ConjS φ₁ φ₂ -> DisyS (negS φ₁) (negS φ₂)
          DisyS φ₁ φ₂ -> ConjS (negS φ₁) (negS φ₂)
          A ф -> E $ negP ф
          E ф -> A $ negP ф


negP::PathF->PathF
negP ф = case ф of
          St φ -> St $ negS φ 
          ConjP ф₁ ф₂ -> DisyP (negP ф₁) (negP ф₂)
          DisyP ф₁ ф₂ -> ConjP (negP ф₁) (negP ф₂)
          X ф₁ -> X $ negP ф₁
          U ф₁ ф₂ -> V (negP ф₁) (negP ф₂)
          V ф₁ ф₂ -> U (negP ф₁) (negP ф₂)



bot = Var ""
top = Neg ""

opG::PathF->PathF
opG ф = case ф of
         -- GGф ≡ Gф
         V (St (Var "")) ф₁ -> opG ф₁
         -- GFGф ≡ FGф
         U (St (Neg "")) (V (St (Var "")) ф₁) -> opF $ opG $ ф₁
         _ -> V (St bot) ф

opF::PathF->PathF
opF ф = case ф of
         -- FFф ≡ Fф
         U (St (Neg "")) ф₁ -> opF ф₁
         -- FGFф ≡ GFф
         V (St (Var "")) (U (St (Neg "")) ф₁) -> opG $ opF ф₁
         _ -> U (St top) ф  

impP::PathF->PathF->PathF
impP ф₁ ф₂ = if ф₁==ф₂ then St top else DisyP (negP ф₁) ф₂

impS::StateF->StateF->StateF
impS φ₁ φ₂ = if φ₁==φ₂ then top else DisyS (negS φ₁) φ₂



data Assertion = Assrt (State, Set PathF) deriving (Eq, Ord)

deleteF::PathF->Assertion->Assertion
deleteF ф (Assrt (s,_Φ)) = Assrt (s,delete ф _Φ)

insertF::PathF->Assertion->Assertion
insertF ф (Assrt (s,_Φ)) = Assrt (s,insert ф _Φ)


data Subgoals = T | Subg [Assertion] deriving Show


subgoals::KripkeS->Assertion->Subgoals
subgoals ks@(KS (_,r,_)) σ@(Assrt (s,_Φ)) =
    if _Φ == empty
    then Subg []
    else let ф = elemAt 0 _Φ in
         case ф of
           St φ -> if eval_modchkCTLS (ks,s) φ then T else Subg [deleteF ф σ]
           DisyP ф₁ ф₂ -> Subg [insertF ф₁ $ insertF ф₂ $ deleteF ф σ]
           ConjP ф₁ ф₂ -> -- ф∧ф ≡ ф
                        if ф₁==ф₂
                        then Subg [insertF ф₁ $ deleteF ф σ]
                        else Subg [insertF ф₁ $ deleteF ф σ,
                                   insertF ф₂ $ deleteF ф σ]
           U ф₁ ф₂ -> -- фUф ≡ ф
                    if ф₁==ф₂ 
                    then Subg [insertF ф₁ $ deleteF ф σ]
                    else -- ф₁Uф₂ ≡ (ф₁∨ф₂)∧(ф₂∨(X(ф₁Uф₂)))
                         Subg [insertF ф₁ $ insertF ф₂ $ deleteF ф σ,
                               insertF ф₂ $ insertF (X ф) $ deleteF ф σ]
           V ф₁ ф₂ -> -- фRф ≡ ф
                    if ф₁==ф₂
                    then Subg [insertF ф₁ $ deleteF ф σ]
                    else -- ф₁Rф₂ ≡ ф₂∧(ф₁∨(X(ф₁Rф₂)))
                         Subg [insertF ф₂ $ deleteF ф σ,
                               insertF ф₁ $ insertF (X ф) $ deleteF ф σ]
           X _ -> -- (Xф₁)∨(Xф₂)∨⋯∨(Xф_n) ≡ X(ф₁∨ф₂∨⋯∨ф_n)
                  let _Φ₁ = Data.Set.map (\(X ф) -> ф) _Φ in
                  Subg [Assrt (s',_Φ₁) | s' <- r s]


check_success::[Assertion]->Bool
check_success v = let фs = concat [toList _Φ | Assrt (_,_Φ) <- v] in
                  (not . null) [V ф₁ ф₂ | V ф₁ ф₂  <- фs, (not . elem ф₂) фs]

{- Strongly Connected Components -}

type DFSn = Int
type Low = Int
type Valid = [(PathF, Int)]
type Stack = [Assertion]
type V = Set Assertion
type F = Set Assertion
type StateDFS = (DFSn, Assertion->(DFSn, Low, Valid), Stack, V, F, Bool)


-- initial state of dfs.
init_state = (0, \_ -> (0, 0, []), [], empty, empty, False)


pushS::Assertion->StateM StateDFS ()
pushS σ = ST $ \(dfsn, i, stack, v, f, b) -> ((), (dfsn, i, σ:stack, v, f, b))

popS::StateM StateDFS Assertion
popS = ST $ \(dfsn, i, σ:stack, v, f, b) -> (σ, (dfsn, i, stack, v, f, b))

inStack::Assertion->StateM StateDFS Bool
inStack σ = ST $ \(dfsn, i, stack, v, f, b) -> (elem σ stack, (dfsn, i, stack, v, f, b))

get_stack::StateM StateDFS Stack
get_stack = ST $ \(dfsn, i, stack, v, f, b) -> (stack, (dfsn, i, stack, v, f, b))

insert_V::Assertion->StateM StateDFS ()
insert_V σ = ST $ \(dfsn, i, stack, v, f, b) -> ((), (dfsn, i, stack, insert σ v, f, b))

elem_V::Assertion->StateM StateDFS Bool
elem_V σ = ST $ \(dfsn, i, stack, v, f, b) -> (member σ v, (dfsn, i, stack, v, f, b))

insert_F::Assertion->StateM StateDFS ()
insert_F σ = ST $ \(dfsn, i, stack, v, f, b) -> ((), (dfsn, i, stack, v, insert σ f, b))

elem_F::Assertion->StateM StateDFS Bool
elem_F σ = ST $ \(dfsn, i, stack, v, f, b) -> (member σ f, (dfsn, i, stack, v, f, b))

set_flag::Bool->StateM StateDFS ()
set_flag b = ST $ \(dfsn, i, stack, v, f, _) -> ((), (dfsn, i, stack, v, f, b))

get_flag::StateM StateDFS Bool
get_flag = ST $ \(dfsn, i, stack, v, f, b) -> (b, (dfsn, i, stack, v, f, b))

get_dfsn::Assertion->StateM StateDFS DFSn
get_dfsn σ = ST $ \(dfsn, i, stack, v, f, b) -> let (d,_,_) = i σ in
                                                (d, (dfsn, i, stack, v, f, b))

get_low::Assertion->StateM StateDFS Low
get_low σ = ST $ \(dfsn, i, stack, v, f, b) -> let (_,lo,_) = i σ in
                                               (lo, (dfsn, i, stack, v, f ,b))

set_low::Assertion->Low->StateM StateDFS ()
set_low σ lo = ST $ \(dfsn, i, stack, v, f, b) -> ((), (dfsn, \σ_ -> if σ_ == σ
                                                                     then let (df, _, va) = i σ in
                                                                          (df, lo, va)
                                                                     else i σ_, stack, v, f, b))

get_valid::Assertion->StateM StateDFS Valid
get_valid σ = ST $ \(dfsn, i, stack, v, f, b) -> let (_,_,va) = i σ in
                                                 (va, (dfsn, i, stack, v, f, b))

set_valid::Assertion->Valid->StateM StateDFS ()
set_valid σ val = ST $ \(dfsn, i, stack, v, f, b) -> ((),(dfsn,\σ_ -> if σ_ == σ
                                                                      then let (df,lo, _) = i σ in
                                                                           (df, lo, val)
                                                                      else i σ_, stack, v, f, b))


init::(Assertion,Valid)->StateM StateDFS ()
init (σ@(Assrt (_,_Φ)), valid) =
    ST $ \(dfsn, i, stack, v, f, b) ->
        ((), (dfsn+1, \σ1 -> if σ1 == σ
                             then (dfsn+1, dfsn+1, let фs = toList _Φ in
                                                   init_valid (dfsn+1)
                                                   (nub $
                                                    [V ф₁ ф₂  | V ф₁ ф₂ <- фs, (not . elem ф₂) фs] ++
                                                    [V ф₁ ф₂  | X (V ф₁ ф₂) <- фs, (not . elem ф₂) фs]))
                             else i σ1, stack, v, f, b))
    where
      init_valid dfsn rs = case rs of
                             []   -> []
                             ф:фs -> let x = [sp | (ф_,sp) <- valid, ф_==ф] in
                                     case x of
                                       []   -> (ф, dfsn):(init_valid dfsn фs)
                                       sp:_ -> (ф, sp):(init_valid dfsn фs)


dfs::(Assertion,Valid)->KripkeS->StateM StateDFS Bool
dfs (σ,valid) ks = 
    do
     set_flag True
     Core.init(σ,valid)
     pushS σ
     insert_V σ
     case subgoals ks σ of
       T       -> set_flag True
       Subg σs -> case σs of
                    [] -> set_flag False
                    _  -> forM_ σs (\σ1 -> do
                                            flag <- get_flag
                                            when flag $ do
                                                         σ1_in_V <- elem_V σ1
                                                         if σ1_in_V 
                                                         then do
                                                               σ1_in_F <- elem_F σ1
                                                               if σ1_in_F
                                                               then set_flag False
                                                               else do 
                                                                     σ1_in_stack <- inStack σ1
                                                                     when σ1_in_stack 
                                                                        (do
                                                                          σ_low  <- get_low σ
                                                                          σ1_low <- get_low σ1
                                                                          set_low σ (min σ_low σ1_low)
                                                                          σ_valid <- get_valid σ
                                                                          σ1_dfsn <- get_dfsn σ1
                                                                          set_valid σ [(r,sp) | (r,sp) <- σ_valid, sp <= σ1_dfsn]
                                                                          σ_valid <- get_valid σ
                                                                          when (null σ_valid)
                                                                            (set_flag False))
                                                         else do
                                                               σ_valid  <- get_valid σ
                                                               flag_dfs <- dfs(σ1,σ_valid) ks
                                                               set_flag flag_dfs
                                                               σ1_low <- get_low σ1
                                                               σ_dfsn <- get_dfsn σ
                                                               when (σ1_low <= σ_dfsn)
                                                                  (do 
                                                                    σ_low <- get_low σ
                                                                    set_low σ (min σ_low σ1_low)
                                                                    σ1_valid <- get_valid σ1
                                                                    set_valid σ σ1_valid))
     σ_dfsn <- get_dfsn σ
     σ_low  <- get_low σ
     when (σ_dfsn == σ_low)
        (do
          stack <- get_stack
          let stack' = σ : takeWhile (σ /=) stack
          forM_ stack' (\_ -> popS)
          flag <- get_flag
          when (not flag)
            (forM_ stack' (\σ_ -> insert_F σ_)))
     flag <- get_flag;
     return flag

-- LTL model checker.
modchkLTL::Assertion->KripkeS->StateM StateDFS Bool
modchkLTL σ ks = dfs(σ,[]) ks

eval_modchkLTL::Assertion->KripkeS->Bool
eval_modchkLTL σ ks = evalStateM (modchkLTL σ ks) init_state

-- CTL★ model checker.
modchkCTLS::Assertion->KripkeS->StateM StateDFS Bool
modchkCTLS σ@(Assrt (s,_Φ)) ks@(KS (_,_,l)) =
    do
     σ_in_V <- elem_V σ
     if σ_in_V 
     then do
           σ_in_F <- elem_F σ
           if σ_in_F 
           then set_flag False
           else set_flag True
     else insert_V σ
     let St φ = elemAt 0 _Φ
     case φ of
       Var a -> update (l s a)
       Neg a -> update ((not . l s) a)
       ConjS φ₁ φ₂ -> do
                      b1 <- modchkCTLS (Assrt (s,singleton $ St φ₁)) ks
                      b2 <- modchkCTLS (Assrt (s,singleton $ St φ₂)) ks
                      update (b1 && b2)
       DisyS φ₁ φ₂ -> do
                      b1 <- modchkCTLS (Assrt (s,singleton $ St φ₁)) ks
                      b2 <- modchkCTLS (Assrt (s,singleton $ St φ₂)) ks
                      update (b1 || b2)
       A ф -> do
               b <- modchkLTL (Assrt (s,singleton ф)) ks
               update b
       E ф -> do
               b <- modchkLTL (Assrt (s,(singleton . negP) ф)) ks
               update (not b)
     flag <- get_flag
     return flag
    where 
        update b = do {set_flag b;when (not b) (insert_F σ)}


eval_modchkCTLS::(KripkeS,State)->StateF->Bool
eval_modchkCTLS (ks,s) φ = evalStateM (modchkCTLS (Assrt (s, singleton $ St φ)) ks) init_state


{-====================================================================================-}

{- Show instances -}

instance Show Assertion where
   show (Assrt (s,_Φ)) = "s" ++ show s ++ " ⊢ " ++ (show $ toList _Φ)


instance Show StateF where
   show sf = case sf of
             -- Variables
              Var "" -> "⊥"
              Var a -> a
              Neg "" -> "┬"
              Neg a -> "¬"++a
             -- Conjunction
              ConjS (Var p) (Var q) -> p++" ⋀ "++q
              ConjS (Neg p) (Neg q) -> "¬"++p++" ⋀ ¬"++q
              ConjS s1 (Var q) -> case s1 of
                                    Neg p -> show s1++" ⋀ "++q
                                    _ -> "("++show s1++") ⋀ "++q
              ConjS (Var p) s2 -> case s2 of
                                    Neg q -> p++" ⋀ ¬"++q
                                    _ -> p++" ⋀ ("++show s2++")"
              ConjS s1@(Neg p) s2 -> show s1++" ⋀ ("++show s2++")"
              ConjS s1 s2@(Neg q) -> "("++show s1++") ⋀ "++show s2
              ConjS s1 s2 -> "("++show s1++") ⋀ ("++show s2++")"
             -- Disjunction
              DisyS (Var p) (Var q) -> p++" ⋁ "++q
              DisyS (Neg p) (Neg q) -> "¬"++p++" ⋁ ¬"++q
              DisyS s1 (Var q) -> case s1 of
                                    Neg p -> show s1++" ⋁ "++q
                                    _ -> "("++show s1++") ⋁ "++q
              DisyS (Var p) s2 -> case s2 of
                                    Neg q -> p++" ⋁ ¬"++q
                                    _ -> p++" ⋁ ("++show s2++")"
              DisyS s1@(Neg p) s2 -> show s1++" ⋁ ("++show s2++")"
              DisyS s1 s2@(Neg q) -> "("++show s1++") ⋁ "++show s2
              DisyS s1 s2 -> "("++show s1++") ⋁ ("++show s2++")"
             -- ForAll
              A p -> case p of
                      X p' -> "AX "++show p'
                      U (St (Neg "")) p' -> "AF "++show p'
                      V (St (Var "")) p' -> "AG "++show p'
                      _ -> "A["++show p++"]"
             -- Exists
              E p -> case p of
                      X p' -> "EX "++show p'
                      U (St (Neg "")) p' -> "EF "++show p'
                      V (St (Var "")) p' -> "EG "++show p'
                      _ -> "E["++show p++"]"


instance Show PathF where
   show p = case p of
             -- State Formulas
             St s -> case s of
                     Var _ -> show s
                     Neg _ -> show s
                     _ -> "("++show s++")"
             -- Conjunction
             ConjP p1@(St _) p2@(St _) -> show p1++" ⋀ "++show p2
             ConjP p1@(St _) p2 -> show p1++" ⋀ ("++show p2++")"
             ConjP p1 p2@(St _) -> "("++show p1++") ⋀ "++show p2
             ConjP p1 p2 -> "("++show p1++") ⋀ ("++show p2++")"
             -- Disjunction
             DisyP p1@(St _) p2@(St _) -> show p1++" ⋁ "++show p2
             DisyP p1@(St _) p2 -> show p1++" ⋁ ("++show p2++")"
             DisyP p1 p2@(St _) -> "("++show p1++") ⋁ "++show p2
             DisyP p1 p2 -> "("++show p1++") ⋁ ("++show p2++")"
             -- neXt state
             X q -> case q of
                     St s@(Var _) -> "X"++show s
                     St s@(Neg _) -> "X"++show s
                     St s@(_)     -> "X"++show q
                     X q1 -> "X"++show q
                     _ -> "X("++show q++")"
             -- Until
             U (St (Neg "")) p2@(St _) -> "F"++show p2
             U (St (Neg "")) p2 -> "F("++show p2++")"
             U p1@(St _) p2@(St _) -> show p1++" U "++show p2
             U p1@(St _) p2 -> show p1++" U ("++show p2++")"
             U p1 p2@(St _) -> "("++show p1++") U "++show p2
             U p1 p2 -> "("++show p1++") U ("++show p2++")"
             -- Velease
             V (St (Var "")) p2@(St _) -> "G"++show p2
             V (St (Var "")) p2 -> "G("++show p2++")"
             V p1@(St _) p2@(St _) -> show p1++" V "++show p2
             V p1@(St _) p2 -> show p1++" V ("++show p2++")"
             V p1 p2@(St _) -> "("++show p1++") V "++show p2
             V p1 p2 -> "("++show p1++") V ("++show p2++")"

