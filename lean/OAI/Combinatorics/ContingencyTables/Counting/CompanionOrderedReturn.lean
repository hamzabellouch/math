import OAI.Combinatorics.ContingencyTables.Counting.CompanionBoundedWalkProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionCappedReturnProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionComputedProposal

namespace OAI

/-! # The return scan in the computed paired-coordinate order -/

namespace ContingencyTables.CompanionOrderedReturn

open MatchingFPRAS.TreeTyped CompanionBoundedWalkProgram CompanionTraceProgram
open CompanionCappedReturnProgram CompanionComputedProposal

abbrev Input := CompanionBoundedWalkProgram.State × List (List Bool)

def scanInput (z : Input) : TotalReturnInput :=
  ((PairedCatalogProgram.catalog z.1.2,history z),z.1.2)
def scanInputRealizer : Realizer scanInput :=
  pair (pair (composition (f := fun z : Input => z.1.2) (g := PairedCatalogProgram.catalog)
      (composition first second) PairedCatalogProgram.catalogRealizer)
    historyRealizer) (composition first second)
lemma polynomial_scanInput : PolynomialTime scanInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_second) PairedCatalogProgram.polynomial_catalog)
    polynomial_history) (polynomial_composition polynomial_first polynomial_second)

def output (z : Input) : List ℕ := totalReturnCode (scanInput z)
def outputRealizer : Realizer output :=
  composition (f := scanInput) (g := totalReturnCode) scanInputRealizer totalReturnCodeRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_scanInput polynomial_totalReturnCode

noncomputable section
open CommonBasesFPRAS CompanionFactorialApplication CompanionArithmeticProposal
open CompanionOrderedProposal CompanionBooleanPhase CompanionTraceWords TwoLiftStates
open scoped Classical
variable {I J : Type} [Fintype I] [Fintype J]

lemma plainTest_ordered (A : Instance I J) {p q : ℕ} (g : Fin p ≃ Labels A)
    (e : (Labels A × Bool) ≃ Fin q) (S : Set (Labels A × Bool)) :
    pairedPlainTest (orderedCatalog A g e,encodeSet e S)=true ↔ PlainState pairs S :=
  CompanionPhaseCounts.plainTest_ordered A g e S

lemma firstPlainCode_ordered (A : Instance I J) {p q : ℕ} (g : Fin p ≃ Labels A)
    (e : (Labels A × Bool) ≃ Fin q) (xs : List (CompanionBooleanPhase.State A)) :
    firstPlainCode (orderedCatalog A g e,xs.map (fun S => encodeSet e S.val))=
      (firstHit (plainPredicate pairs) xs).map (fun T => encodeSet e T.val.val) := by
  induction xs with
  | nil => simp only [firstPlainCode,List.map_nil,List.filter_nil,List.getElem?_nil,firstHit,Option.map_none]
  | cons S xs ih =>
    unfold firstPlainCode at ih ⊢
    simp only [List.map_cons,List.filter_cons,firstHit]
    by_cases h : PlainState pairs S.val
    · have ht := (plainTest_ordered A g e S.val).mpr h
      simp only [ht,ite_true,plainPredicate,dite_eq_left h,Option.map_some,List.getElem?_cons_zero]
    · have ht : pairedPlainTest (orderedCatalog A g e,encodeSet e S.val)=false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        exact h ((plainTest_ordered A g e S.val).mp ht)
      simpa only [ht,Bool.false_eq_true,ite_false,plainPredicate,dite_eq_right h] using ih

theorem totalReturnCode_ordered (A : Instance I J) {p q : ℕ} (g : Fin p ≃ Labels A)
    (e : (Labels A × Bool) ≃ Fin q)
    (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)))
    (xs : List (CompanionBooleanPhase.State A)) :
    totalReturnCode ((orderedCatalog A g e,xs.map (fun T => encodeSet e T.val)),encodeSet e S.val.val)=
      encodeSet e (CompanionCappedReturn.returnDefault (plainPredicate pairs) S xs).val.val := by
  unfold totalReturnCode returnCode
  rw [←List.map_tail,firstPlainCode_ordered]
  unfold CompanionCappedReturn.returnDefault
  cases firstHit (plainPredicate pairs) xs.tail <;> rfl

end
end ContingencyTables.CompanionOrderedReturn

end OAI
