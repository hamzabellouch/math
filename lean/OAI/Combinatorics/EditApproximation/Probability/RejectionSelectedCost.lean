import OAI.Combinatorics.EditApproximation.Probability.RejectionArrayLaw
import OAI.Combinatorics.EditApproximation.Probability.FreshCoordinateCost
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Rejection counts are independent of all accepted values. Thus even
an adaptive choice of coordinates incurs fewer than two word trials per
selected coordinate in expectation. No unused source is charged. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Selected

variable {ι : Type*} [Fintype ι] (range : ι → ℕ) [∀ i, NeZero (range i)]



instance rejectionAcceptedLaw_probability : IsProbabilityMeasure (rejectionAcceptedLaw range) := by
  unfold rejectionAcceptedLaw
  infer_instance



instance rejectionFailureLaw_probability (i : ι) : IsProbabilityMeasure (rejectionFailureLaw range i) := by
  unfold rejectionFailureLaw
  infer_instance





instance rejectionRuntimeArrayLaw_probability : IsProbabilityMeasure (rejectionRuntimeArrayLaw range) := by
  unfold rejectionRuntimeArrayLaw rejectionAcceptedLaw
  infer_instance

 theorem rejectionRuntimeArrayLaw_accepted :
    (rejectionRuntimeArrayLaw range).map Prod.snd = rejectionAcceptedLaw range := by
  unfold rejectionRuntimeArrayLaw
  simp



 theorem rejectionFailureArray_bits_integrable (i : ι) :
    Integrable (fun failures : ι → ℕ => ((failures i : ℝ) + 1) * rejectionBitCount (range i))
      (Measure.pi (rejectionFailureLaw range)) := by
  apply integrable_comp_eval (X := fun _ : ι => ℕ) (μ := rejectionFailureLaw range) (i := i)
    (f := fun failures : ℕ => ((failures : ℝ) + 1) * rejectionBitCount (range i))
  exact (rejection_trials_integrable (range i) (2 ^ rejectionBitCount (range i))
    (Nat.pos_of_ne_zero (NeZero.ne (range i)))
    (rejectionWord_range (range i) (Nat.pos_of_ne_zero (NeZero.ne (range i)))).1).mul_const _

 theorem rejectionSelectedBits_integrable (selected : ι → (∀ i, Fin (range i)) → Prop) :
    Integrable (rejectionSelectedBits range selected) (rejectionRuntimeArrayLaw range) := by
  classical
  unfold rejectionSelectedBits rejectionRuntimeArrayLaw
  apply integrable_finsetSum
  intro i _
  exact (rejectionFailureArray_bits_integrable range i).mul_prod (Integrable.of_finite (μ := rejectionAcceptedLaw range)
    (f := fun accepted => selectionIndicator (selected i accepted)))

 theorem rejectionSelectedBits_expected_le
    (selected : ι → (∀ i, Fin (range i)) → Prop) (budget : ℝ)
    (hbudget : ∀ accepted, ∑ i, (rejectionBitCount (range i) : ℝ) *
      selectionIndicator (selected i accepted) ≤ budget) :
    (∫ execution, rejectionSelectedBits range selected execution ∂rejectionRuntimeArrayLaw range) ≤
      2 * budget := by
  classical
  unfold rejectionSelectedBits rejectionRuntimeArrayLaw
  rw [integral_finsetSum]
  · have hprod (i : ι) :
        (∫ execution : RejectionRuntimeArray range,
          (((execution.1 i : ℝ) + 1) * rejectionBitCount (range i)) *
            selectionIndicator (selected i execution.2)
          ∂(Measure.pi (rejectionFailureLaw range)).prod (rejectionAcceptedLaw range)) =
        (∫ failures : ι → ℕ, ((failures i : ℝ) + 1) * rejectionBitCount (range i)
          ∂Measure.pi (rejectionFailureLaw range)) *
        (∫ accepted, selectionIndicator (selected i accepted) ∂rejectionAcceptedLaw range) :=
      integral_prod_mul (μ := Measure.pi (rejectionFailureLaw range))
        (ν := rejectionAcceptedLaw range)
        (fun failures : ι → ℕ => ((failures i : ℝ) + 1) * rejectionBitCount (range i))
        (fun accepted : ∀ i, Fin (range i) => selectionIndicator (selected i accepted))
    simp_rw [hprod]
    have hcost (i : ι) :
        (∫ failures : ι → ℕ, ((failures i : ℝ) + 1) * rejectionBitCount (range i)
          ∂Measure.pi (rejectionFailureLaw range)) ≤ 2 * rejectionBitCount (range i) := by
      rw [integral_comp_eval (X := fun _ : ι => ℕ) (μ := rejectionFailureLaw range) (i := i)
        (f := fun failures : ℕ => ((failures : ℝ) + 1) * rejectionBitCount (range i))
        (by fun_prop)]
      exact rejection_consumed_bits_moment (range i) (Nat.pos_of_ne_zero (NeZero.ne (range i)))
    calc
      _ ≤ ∑ i, (2 * rejectionBitCount (range i)) *
          (∫ accepted, selectionIndicator (selected i accepted) ∂rejectionAcceptedLaw range) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right (hcost i)
        exact integral_nonneg (fun _ => by unfold selectionIndicator; split_ifs <;> norm_num)
      _ = 2 * (∫ accepted, ∑ i, (rejectionBitCount (range i) : ℝ) *
          selectionIndicator (selected i accepted) ∂rejectionAcceptedLaw range) := by
        rw [integral_finsetSum]
        · simp only [integral_const_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        · intro i _
          exact Integrable.of_finite
      _ ≤ 2 * budget := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (integral_mono Integrable.of_finite (integrable_const _) hbudget).trans_eq (by simp [rejectionAcceptedLaw])
  · intro i _
    exact (rejectionFailureArray_bits_integrable range i).mul_prod (Integrable.of_finite (μ := rejectionAcceptedLaw range)
    (f := fun accepted => selectionIndicator (selected i accepted)))

end Selected

end EditApproximation

end OAI
