import OAI.Combinatorics.ContingencyTables.Machines.CompletionEnumerationProgram

namespace OAI

/-! # Enumerating only the short proposal word -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def digitBool (a : ℕ) : Bool := decide (a=1)

def digitBoolRealizer : Realizer digitBool := composition (pair identity (constant 1)) natEqual

lemma polynomial_digitBool : PolynomialTime digitBoolRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 1))
    polynomial_natEqual

def booleanWords (xs : List Bool) : List (List Bool) :=
  (gridWords (xs,2)).map (List.map digitBool)

def booleanWordsRealizer : Realizer booleanWords :=
  composition (composition (pair identity (constant 2)) gridWordsRealizer)
    (map (map digitBoolRealizer))

lemma work_booleanWords : WorkBound booleanWordsRealizer
    (fun xs => gridStateCount (xs,2)+weight xs) := by
  have hi : WorkBound (pair (identity (A := List Bool)) (constant 2))
      (fun xs => gridStateCount (xs,2)+weight xs) :=
    work_of_polynomial (polynomial_pair polynomial_identity (polynomial_constant 2))
      Polynomial.X (fun xs => by simp)
  have hg : WorkBound (composition (pair (identity (A := List Bool)) (constant 2))
      gridWordsRealizer) (fun xs => gridStateCount (xs,2)+weight xs) := by
    apply work_composition hi work_gridWords (Polynomial.X+10)
    intro xs
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,weight_prod,id_eq]
    have hc : weight (2:ℕ)≤9 := by simpa using weight_nat_numeric 2
    omega
  unfold booleanWordsRealizer
  exact work_then_polynomial hg (polynomial_map (polynomial_map polynomial_digitBool))

def booleanEnumeration (s : ℕ) : Fin (2^s) ≃ (Fin s → Bool) :=
  finFunctionFinEquiv.symm.trans (Equiv.piCongrRight (fun _ => finTwoEquiv))

lemma booleanWords_of_length (xs : List Bool) (s : ℕ) (hs : xs.length=s) :
    booleanWords xs=List.ofFn (fun k => List.ofFn (booleanEnumeration s k)) := by
  unfold booleanWords
  rw [gridWords_finFunctions xs 1 s hs,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  dsimp only [Function.comp_apply]
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change digitBool ((finFunctionFinEquiv.symm k) i).val=
    finTwoEquiv ((finFunctionFinEquiv.symm k) i)
  have hb (a : Fin 2) : digitBool a.val=finTwoEquiv a := by
    fin_cases a <;> rfl
  exact hb _

lemma sum_booleanWords (xs : List Bool) (s : ℕ) (hs : xs.length=s)
    (w : List Bool → ℕ) :
    ((booleanWords xs).map w).sum=∑ bits : Fin s → Bool,w (List.ofFn bits) := by
  rw [booleanWords_of_length xs s hs,List.map_ofFn,List.sum_ofFn]
  exact (booleanEnumeration s).sum_comp (fun bits => w (List.ofFn bits))

end ContingencyTables.DensePrograms

end OAI
