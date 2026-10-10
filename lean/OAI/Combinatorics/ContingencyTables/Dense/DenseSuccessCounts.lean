import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerLaw

namespace OAI

/-! # One entry per accepted dense table, with no trial-fibre enumeration -/

namespace ContingencyTables.GridBoundary
open FairBits
open scoped BigOperators Classical
noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

/-- The unique bin-offset trial for a table supplies its entire success
count. This removes a sum over all trials from each output lookup. -/
theorem denseTrial_success_count (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I×J ≃ Fin q) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) (X : Table R P) :
    ((denseTrialCounts R P d hd hR hP e h a).push (trialSuccess R P d e htotal)).count
      (some X)=
    (denseTrialCounts R P d hd hR hP e h a).count (tableTrial R P d hd hR hP e X) := by
  change (∑ t,if trialSuccess R P d e htotal t=some X then
    (denseTrialCounts R P d hd hR hP e h a).count t else 0)=_
  simp_rw [trialSuccess_some_iff R P d hd hR hP e htotal]
  simp

/-- The rejected count is determined by the known common denominator
and the accepted table counts, including all invalid completions. -/
theorem denseTrial_failure_count (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I×J ≃ Fin q) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) :
    ((denseTrialCounts R P d hd hR hP e h a).push (trialSuccess R P d e htotal)).count none=
      2^denseTrialBits R P d e h-
        ∑ X : Table R P,(denseTrialCounts R P d hd hR hP e h a).count
          (tableTrial R P d hd hR hP e X) := by
  have ht := ((denseTrialCounts R P d hd hR hP e h a).push
    (trialSuccess R P d e htotal)).total
  rw [Fintype.sum_option] at ht
  simp_rw [denseTrial_success_count R P d hd hR hP e htotal] at ht
  omega

/-- Evaluation uses one propagated bin numerator and one product of
closed-form offset counts; it never enumerates the acceptance bits. -/
theorem denseTrial_table_count (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I×J ≃ Fin q) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) (X : Table R P) :
    (denseTrialCounts R P d hd hR hP e h a).count (tableTrial R P d hd hR hP e X)=
      IntegerPropagation.numerators (denseTransitionCount R P d e) a (d^50*(h+1)^2)
        (tableTrial R P d hd hR hP e X).1 *
      ∏ j : Fin q,OffsetCountPrograms.offsetCount
        ((integerWidth R P d (e.symm j),
          2^offsetBitLength (integerWidth R P d (e.symm j)) h d),
          ((offsetCoordinateEquiv e (integerWidth R P d)).symm
            (tableTrial R P d hd hR hP e X).2 j).val) := rfl

end
end ContingencyTables.GridBoundary

end OAI
