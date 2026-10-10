import OAI.Combinatorics.ContingencyTables.Machines.InitialChoiceProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionArithmeticProposal
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteCollections
import Mathlib.Data.List.NodupEquivFin

namespace OAI

/-! # Canonical paired-label order for the initial binary program

The order is the explicit list of cells, then their copies, then the
two sides of each pair. The code is obtained directly from the sampled
Boolean rows, so no enumeration of the set-valued state space occurs.
-/

namespace ContingencyTables.CanonicalInitialEncoding

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CommonBasesFPRAS InitialTransversals FixedCardinalityMixture InitialFactorialBits
open scoped BigOperators Classical

def pairValue (b : Bool) : List ℕ := [if b then 1 else 0,if b then 0 else 1]

def pairValueRealizer : Realizer pairValue :=
  composition (pair (choose identity (constant 1) (constant 0))
    (composition (pair (choose identity (constant 0) (constant 1)) (constant [])) listCons)) listCons

theorem polynomial_pairValue : PolynomialTime pairValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_choose polynomial_identity (polynomial_constant 1) (polynomial_constant 0))
    (polynomial_composition (polynomial_pair
      (polynomial_choose polynomial_identity (polynomial_constant 0) (polynomial_constant 1))
      (polynomial_constant [])) polynomial_listCons)) polynomial_listCons

def pairedCode (rows : List (List Bool)) : List ℕ := rows.flatten.flatMap pairValue

def pairedCodeRealizer : Realizer pairedCode := composition flatten (flatMapPoly pairValueRealizer)

theorem polynomial_pairedCode : PolynomialTime pairedCodeRealizer :=
  polynomial_composition polynomial_flatten (polynomial_flatMapPoly polynomial_pairValue)

def initialCode (z : InitialChoiceProgram.Input) : List ℕ := pairedCode (InitialChoiceProgram.choiceCode z)

def initialCodeRealizer : Realizer initialCode :=
  composition InitialChoiceProgram.choiceCodeRealizer pairedCodeRealizer

theorem polynomial_initialCode : PolynomialTime initialCodeRealizer :=
  polynomial_composition InitialChoiceProgram.polynomial_choiceCode polynomial_pairedCode

noncomputable section
variable {q : ℕ} (b : Fin q → ℕ)

def copyOrder : List (Copy b) := (List.finRange q).sigma (fun i => List.finRange (b i))

def pairOrder : List (Copy b×Bool) := (copyOrder b).product [false,true]

lemma copyOrder_nodup : (copyOrder b).Nodup :=
  (List.nodup_finRange q).sigma (fun i => List.nodup_finRange (b i))

lemma copyOrder_mem (p : Copy b) : p∈copyOrder b := by
  rcases p with ⟨i,k⟩
  simp [copyOrder]

lemma pairOrder_nodup : (pairOrder b).Nodup :=
  (copyOrder_nodup b).product (by decide)

lemma pairOrder_mem (p : Copy b×Bool) : p∈pairOrder b := by
  rcases p with ⟨p,t⟩
  have hp := copyOrder_mem b p
  cases t <;> simp [pairOrder,hp]

def coordinateEquiv : (Copy b×Bool) ≃ Fin (pairOrder b).length :=
  (List.Nodup.getEquivOfForallMemList (pairOrder b) (pairOrder_nodup b) (pairOrder_mem b)).symm

lemma coordinateOrder : List.ofFn (coordinateEquiv b).symm=pairOrder b := by
  change List.ofFn (pairOrder b).get=pairOrder b
  exact List.ofFn_get (pairOrder b)

lemma encodeSet_eq_map (S : Set (Copy b×Bool)) :
    CompanionArithmeticProposal.encodeSet (coordinateEquiv b) S=
      (pairOrder b).map (fun p => if p∈S then 1 else 0) := by
  have h := congrArg (List.map (fun p => if p∈S then (1:ℕ) else 0)) (coordinateOrder b)
  rw [List.map_ofFn] at h
  exact h

lemma pairedCode_eq_map (v : ∀ i,Fin (b i) → Bool) :
    pairedCode (List.ofFn (fun i => List.ofFn (v i)))=
      (pairOrder b).map (fun p => if p∈encode b (fun i => subsetEquiv (b i) (v i)) then 1 else 0) := by
  simp only [pairedCode,pairOrder,copyOrder,List.sigma,List.product,List.ofFn_eq_map,
    List.flatten_eq_flatMap,List.flatMap_map,List.flatMap_assoc,List.map_flatMap,List.map_map]
  apply List.flatMap_congr
  intro i _
  simp only [id_eq,List.flatMap_map,Function.comp_def]
  apply List.flatMap_congr
  intro k _
  cases hv : v i k <;>
    simp [pairValue,subsetEquiv,hv]

/-- The explicit paired list order gives the same encoded set as the
semantic local choices, including cells of capacity zero. -/
theorem pairedCode_encode (v : ∀ i,Fin (b i) → Bool) :
    pairedCode (List.ofFn (fun i => List.ofFn (v i)))=
      CompanionArithmeticProposal.encodeSet (coordinateEquiv b)
        (encode b (fun i => subsetEquiv (b i) (v i))) := by
  rw [encodeSet_eq_map]
  exact pairedCode_eq_map b v

theorem initialCode_ofFn (B : ℕ) (hB : 0<B) (bits : Fin (bitCount b B) → Bool) :
    initialCode ((List.ofFn b,B),List.ofFn bits)=
      CompanionArithmeticProposal.encodeSet (coordinateEquiv b) (encode b (drawChoices b B bits)) := by
  unfold initialCode
  rw [InitialChoiceProgram.choiceCode_ofFn b B hB bits]
  exact pairedCode_encode b (fun i => FixedCardinalityMixture.vectorDraw B (b i) (wordEquiv b B bits i))

end
end ContingencyTables.CanonicalInitialEncoding

end OAI
