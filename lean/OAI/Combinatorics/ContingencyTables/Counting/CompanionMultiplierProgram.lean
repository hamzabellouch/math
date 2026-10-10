import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseCounts
import OAI.Combinatorics.MatchingCount.Complexity.TreeFractionCosts

namespace OAI

/-! # A binary rational program for each learned multiplier

The two observed frequencies have the same trajectory length, which
cancels before division. Thus one multiplication by the ratio of the
actual integer counts implements the exact rational update, including
the zero-denominator behavior on unsuccessful histories.
-/

namespace ContingencyTables.CompanionMultiplierProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionPhaseCounts CompanionFactorialApplication CompanionRationalUpdates
open CompanionOrderedProposal CompanionArithmeticProposal CommonBasesFPRAS
open scoped Classical

def countRatio (z : DefectCountInput) : TreeFraction.Fraction :=
  (plainCountCode z.1,defectCountCode z)

def countPlainRealizer : Realizer (fun z : DefectCountInput => plainCountCode z.1) :=
  composition (f := fun z : DefectCountInput => z.1) (g := plainCountCode)
    first plainCountRealizer

def countRatioRealizer : Realizer countRatio :=
  pair countPlainRealizer defectCountRealizer

lemma polynomial_countRatio : PolynomialTime countRatioRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_plainCount)
    polynomial_defectCount

abbrev UpdateInput := DefectCountInput×TreeFraction.Fraction

def updateCode (z : UpdateInput) : TreeFraction.Fraction :=
  if z.1.2.1=z.1.2.2 then z.2 else TreeFraction.mul (z.2,countRatio z.1)

def diagonalRealizer : Realizer (fun z : UpdateInput => decide (z.1.2.1=z.1.2.2)) :=
  composition (pair (composition (composition first second) first)
    (composition (composition first second) second)) natEqual

lemma polynomial_diagonal : PolynomialTime diagonalRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_second)) polynomial_natEqual

def updateCodeRealizer : Realizer updateCode :=
  (choose diagonalRealizer second
    (composition (pair second (composition first countRatioRealizer)) TreeFraction.mulRealizer)).congr
      (by intro z; simp only [updateCode,Function.comp_apply,decide_eq_true_eq])

theorem polynomial_updateCode : PolynomialTime updateCodeRealizer := by
  unfold updateCodeRealizer
  apply polynomial_congr
  exact polynomial_choose polynomial_diagonal polynomial_second
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_countRatio)) TreeFraction.polynomial_mul)

lemma updateCode_value (z : UpdateInput) :
    TreeFraction.val (updateCode z)=
      if z.1.2.1=z.1.2.2 then TreeFraction.val z.2
      else TreeFraction.val z.2*(plainCountCode z.1.1:ℚ)/(defectCountCode z.1:ℚ) := by
  unfold updateCode
  split_ifs
  · rfl
  · rw [TreeFraction.mul_val]
    simp only [countRatio,TreeFraction.val,mul_div_assoc]

noncomputable section
open TwoLiftStates
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p m : ℕ} (g : Fin p ≃ Labels A)
  (e : (Labels A×Bool) ≃ Fin m)

/-- This is the literal source multiplier update at a pair of actual
labels, not a surrogate recurrence on unrelated rational values. -/
theorem updateCode_learn (states : List (Set (Labels A×Bool)))
    (hlen : 0<states.length) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (i j : Fin p) (hw : 0≤w (pair (g i)) (pair (g j))) :
    TreeFraction.val (updateCode (((orderedCatalog A g e,states.map (encodeSet e)),(i.val,j.val)),
      TreeFraction.repr (w (pair (g i)) (pair (g j)))))=
        rationalLearn pairs w states (pair (g i)) (pair (g j)) := by
  rw [updateCode_value,plainCount_code,defectCount_code,TreeFraction.val_repr hw,
    rationalLearn_counts A w states hlen]
  have hp : pair (g i)∈(pairs : List (CompanionRationalUpdates.Pair A)) := pair_mem _
  have hq : pair (g j)∈(pairs : List (CompanionRationalUpdates.Pair A)) := pair_mem _
  have he : pair (g i)=pair (g j) ↔ i=j :=
    ⟨fun h => g.injective (pair_injective h),fun h => congrArg (fun a => pair (g a)) h⟩
  simp only [hp,hq,true_and]
  by_cases hij : i=j
  · subst j
    simp
  · have hval : i.val≠j.val := fun h => hij (Fin.ext h)
    have hpair : pair (g i)≠pair (g j) := fun h => hij (he.mp h)
    simp only [hval,ite_false]
    split_ifs with h
    · rfl
    · exact (h hpair).elim

end
end ContingencyTables.CompanionMultiplierProgram

end OAI
