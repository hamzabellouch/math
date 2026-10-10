import OAI.Combinatorics.ContingencyTables.Counting.CompanionTraceWords
import OAI.Combinatorics.ContingencyTables.Counting.CompanionNeighborProgram

namespace OAI

/-! # Polynomial code for recognizing and locating a trace return

The paired plain-state test sums the two bits of each label. The return
program scans the supplied path after its initial state; no enumeration
of the exponential paired-state space occurs.
-/

namespace ContingencyTables.CompanionTraceProgram

open CommonBasesFPRAS CompanionChainValidator CompanionArithmeticProposal
open CompanionFactorialApplication CompanionBooleanPhase CompanionTraceWords
open ProfilePrograms MatchingFPRAS.TreeTyped
open scoped Classical

def pairedPlainTest (z : ValidatorInput) : Bool :=
  balancedTest ((z.1.map (fun ij => z.2.getD ij.1 0),
    z.1.map (fun ij => z.2.getD ij.2 0)),1)

def pairedPlainTestRealizer : Realizer pairedPlainTest :=
  composition (pair (pair
    (composition (pair second first) (mapWith pairFirstLookup))
    (composition (pair second first) (mapWith pairSecondLookup))) (constant 1))
    balancedTestRealizer

theorem polynomial_pairedPlainTest : PolynomialTime pairedPlainTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_mapWith polynomial_pairFirstLookup))
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_mapWith polynomial_pairSecondLookup))) (polynomial_constant 1))
    polynomial_balancedTest

abbrev ReturnInput := List (ℕ×ℕ)×List (List ℕ)

def firstPlainCode (z : ReturnInput) : Option (List ℕ) :=
  (z.2.filter (fun xs => pairedPlainTest (z.1,xs)))[0]?

def firstPlainCodeRealizer : Realizer firstPlainCode :=
  composition (composition (filterWith pairedPlainTestRealizer)
    (pair identity (constant 0))) getOptionFast

theorem polynomial_firstPlainCode : PolynomialTime firstPlainCodeRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_filterWith polynomial_pairedPlainTest)
    (polynomial_pair polynomial_identity (polynomial_constant 0))) polynomial_getOptionFast

/-- Strict first return: the initial path entry is omitted. -/
def returnCode (z : ReturnInput) : Option (List ℕ) :=
  firstPlainCode (z.1,z.2.tail)

def returnCodeRealizer : Realizer returnCode :=
  composition (pair first (composition second tail)) firstPlainCodeRealizer

theorem polynomial_returnCode : PolynomialTime returnCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_tail)) polynomial_firstPlainCode

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem pairedPlainTest_encode (A : Instance I J) (S : Set (Labels A×Bool)) :
    pairedPlainTest (pairCatalog A,encodeSet (coordinateEquiv A) S)=true ↔
      PlainState TwoLiftStates.pairs S := by
  unfold pairedPlainTest pairCatalog
  simp only [List.map_ofFn]
  change balancedTest ((List.ofFn (fun i : Fin (Fintype.card (Labels A)) =>
      (encodeSet (coordinateEquiv A) S).getD
        (coordinateEquiv A (labelEquiv A i,false)).val 0),
    List.ofFn (fun i : Fin (Fintype.card (Labels A)) =>
      (encodeSet (coordinateEquiv A) S).getD
        (coordinateEquiv A (labelEquiv A i,true)).val 0)),1)=true ↔ _
  simp only [encodeSet,getD_setProfile,setProfile,coordinateSet,Set.mem_preimage,
    Equiv.symm_apply_apply]
  rw [balancedTest_ofFn,plain_iff_occupancy]
  change (∀ i,TwoLiftStates.occupancy S (labelEquiv A i)=1) ↔
    ∀ p,TwoLiftStates.occupancy S p=1
  constructor
  · intro h p
    simpa only [Equiv.apply_symm_apply] using h ((labelEquiv A).symm p)
  · intro h i
    exact h (labelEquiv A i)

/-- The list program returns the encoding of the same first plain
state as the semantic scan, including the no-return outcome. -/
theorem firstPlainCode_encode (A : Instance I J) (xs : List (State A)) :
    firstPlainCode (pairCatalog A,xs.map (fun S => encodeSet (coordinateEquiv A) S.val))=
      (firstHit (plainPredicate TwoLiftStates.pairs) xs).map
        (fun T => encodeSet (coordinateEquiv A) T.val.val) := by
  induction xs with
  | nil => simp [firstPlainCode,firstHit]
  | cons S xs ih =>
    unfold firstPlainCode at ih ⊢
    simp only [List.map_cons,List.filter_cons,firstHit]
    by_cases h : PlainState TwoLiftStates.pairs S.val
    · have ht : pairedPlainTest (pairCatalog A,encodeSet (coordinateEquiv A) S.val)=true :=
        (pairedPlainTest_encode A S.val).mpr h
      simp only [ht,ite_true,plainPredicate,dite_eq_left h,Option.map_some,List.getElem?_cons_zero]
    · have ht : pairedPlainTest (pairCatalog A,encodeSet (coordinateEquiv A) S.val)=false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        exact h ((pairedPlainTest_encode A S.val).mp ht)
      simpa only [ht,Bool.false_eq_true,ite_false,plainPredicate,dite_eq_right h] using ih

theorem returnCode_encode (A : Instance I J) (xs : List (State A)) :
    returnCode (pairCatalog A,xs.map (fun S => encodeSet (coordinateEquiv A) S.val))=
      (firstHit (plainPredicate TwoLiftStates.pairs) xs.tail).map
        (fun T => encodeSet (coordinateEquiv A) T.val.val) := by
  unfold returnCode
  rw [← List.map_tail]
  exact firstPlainCode_encode A xs.tail

end
end ContingencyTables.CompanionTraceProgram

end OAI
