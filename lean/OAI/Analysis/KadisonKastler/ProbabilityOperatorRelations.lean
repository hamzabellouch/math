import OAI.Analysis.KadisonKastler.ProbabilityOperatorAlgebra

namespace OAI

/-! # Linear relations and commutator bounds under vector integration

The operator fields are only assumed measurable on each vector. Fixed
left and right multiplication commute with their probability integral;
essential operator-norm commutator bounds therefore pass to the integral.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- An explicit bound for a fixed sandwich of a bounded field. -/
theorem ae_norm_operator_sandwich_le
    (μ : Measure S) (F : S → H →L[ℂ] H) {C : ℝ}
    (hF : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (A B : H →L[ℂ] H) :
    ∀ᵐ s ∂μ, ‖A * F s * B‖ ≤ ‖A‖ * C * ‖B‖ := by
  filter_upwards [hF] with s hs
  calc
    ‖A * F s * B‖ ≤ ‖A * F s‖ * ‖B‖ := norm_mul_le _ _
    _ ≤ (‖A‖ * ‖F s‖) * ‖B‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (norm_nonneg _)) (norm_nonneg _)

/-- Fixed operator multiplication commutes with the actual vector integral. -/
theorem probabilityOperatorIntegral_sandwich
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (A B : H →L[ℂ] H) :
    probabilityOperatorIntegral μ (fun s => A * F s * B)
      (fun x => A.continuous.comp_aestronglyMeasurable (hF (B x)))
      (‖A‖ * C * ‖B‖) (ae_norm_operator_sandwich_le μ F hC A B) =
      A * probabilityOperatorIntegral μ F hF C hC * B := by
  apply ContinuousLinearMap.ext
  intro x
  change (∫ s, A (F s (B x)) ∂μ) = A (∫ s, F s (B x) ∂μ)
  exact A.integral_comp_comm (integrable_bounded_operator_vector μ F hF hC (B x))

/-- A uniform almost-everywhere commutator bound survives vector integration. -/
theorem norm_probabilityOperatorIntegral_commutator_le
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (A : H →L[ℂ] H)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcomm : ∀ᵐ s ∂μ, ‖F s * A - A * F s‖ ≤ ε) :
    ‖probabilityOperatorIntegral μ F hF C hC * A -
      A * probabilityOperatorIntegral μ F hF C hC‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro x
  have hi := integrable_bounded_operator_vector μ F hF hC x
  have hiA := integrable_bounded_operator_vector μ F hF hC (A x)
  have hAi : Integrable (fun s => A (F s x)) μ := A.integrable_comp hi
  change ‖(∫ s, F s (A x) ∂μ) - A (∫ s, F s x ∂μ)‖ ≤ ε * ‖x‖
  rw [← A.integral_comp_comm hi, ← integral_sub hiA hAi]
  have hb : ∀ᵐ s ∂μ, ‖F s (A x) - A (F s x)‖ ≤ ε * ‖x‖ := by
    filter_upwards [hcomm] with s hs
    exact ((F s * A - A * F s).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  have hn := norm_integral_le_of_norm_le_const (μ := μ) hb
  simpa only [probReal_univ, mul_one] using hn

omit [CompleteSpace H] in
/-- An algebra approximation bounds every commutator with its commutant. -/
theorem norm_commutator_of_near_commuting
    (T b A : H →L[ℂ] H) {δ : ℝ} (hTb : ‖T - b‖ ≤ δ)
    (hbA : b * A = A * b) : ‖T * A - A * T‖ ≤ 2 * δ * ‖A‖ := by
  have he : T * A - A * T = (T - b) * A - A * (T - b) := by
    rw [sub_mul, mul_sub, hbA]
    abel
  rw [he]
  calc
    _ ≤ ‖(T - b) * A‖ + ‖A * (T - b)‖ := norm_sub_le _ _
    _ ≤ ‖T - b‖ * ‖A‖ + ‖A‖ * ‖T - b‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ δ * ‖A‖ + ‖A‖ * δ := add_le_add
      (mul_le_mul_of_nonneg_right hTb (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hTb (norm_nonneg _))
    _ = _ := by ring

/-- This estimate requires no measurable choice of nearby algebra elements. -/
theorem norm_probabilityOperatorIntegral_commutator_of_near
    (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hC : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (A : H →L[ℂ] H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ᵐ s ∂μ, ∃ b : H →L[ℂ] H, b * A = A * b ∧ ‖F s - b‖ ≤ δ) :
    ‖probabilityOperatorIntegral μ F hF C hC * A -
      A * probabilityOperatorIntegral μ F hF C hC‖ ≤ 2 * δ * ‖A‖ := by
  apply norm_probabilityOperatorIntegral_commutator_le μ F hF C hC A (by positivity)
  filter_upwards [hnear] with s hs
  obtain ⟨b, hbA, hFb⟩ := hs
  exact norm_commutator_of_near_commuting _ b A hFb hbA

end

end KadisonKastler

end OAI
