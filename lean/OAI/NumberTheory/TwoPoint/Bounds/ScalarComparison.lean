import OAI.NumberTheory.TwoPoint.Bounds.DecoderComparison

namespace OAI

/-! Signed scalar expansions preserve their coefficients through comparison. -/

namespace TwoPointCorrelations

open Finset

lemma uniformAverage_mul_const {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformAverage (fun x => c * f x) = c * uniformAverage f := by
  unfold uniformAverage
  rw [← Finset.mul_sum]
  ring

/-- Each event is compared before absolute values are taken. The total error
is weighted by the absolute values of the original signed coefficients. -/
theorem scalar_average_comparison {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    (f : ι → α → ℝ) (g : ι → β → ℝ) (c error : ι → ℝ)
    (h : ∀ i, |uniformAverage (f i) - uniformAverage (g i)| ≤ error i) :
    |uniformAverage (fun x => ∑ i, c i * f i x) -
      uniformAverage (fun y => ∑ i, c i * g i y)| ≤ ∑ i, |c i| * error i := by
  simp_rw [uniformAverage_sum, uniformAverage_mul_const]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |c i * uniformAverage (f i) - c i * uniformAverage (g i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i| * |uniformAverage (f i) - uniformAverage (g i)| := by
      simp_rw [← mul_sub, abs_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (abs_nonneg _))

/-- Uniform event error times total absolute coefficient mass. -/
theorem scalar_average_comparison_uniform {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    (f : ι → α → ℝ) (g : ι → β → ℝ) (c : ι → ℝ) (error : ℝ)
    (h : ∀ i, |uniformAverage (f i) - uniformAverage (g i)| ≤ error) :
    |uniformAverage (fun x => ∑ i, c i * f i x) -
      uniformAverage (fun y => ∑ i, c i * g i y)| ≤ (∑ i, |c i|) * error := by
  simpa only [Finset.sum_mul] using scalar_average_comparison f g c (fun _ => error) h

end TwoPointCorrelations

end OAI
