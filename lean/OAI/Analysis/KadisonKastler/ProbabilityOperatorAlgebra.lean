import OAI.Analysis.KadisonKastler.PoissonVectorAverage

namespace OAI

/-! # Algebra membership of vectorwise probability averages -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem integrable_bounded_operator_vector (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    {C : ℝ} (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (x : H) :
    Integrable (fun s => F s x) μ := by
  apply (integrable_const (C * ‖x‖)).mono' (hm x)
  filter_upwards [hb] with s hs
  exact ((F s).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x))

/-- Every fixed commutation relation passes to the actual vector integral. -/
theorem probabilityOperatorIntegral_commutes (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (T : H →L[ℂ] H)
    (hT : ∀ᵐ s ∂μ, F s * T = T * F s) :
    probabilityOperatorIntegral μ F hm C hb * T =
      T * probabilityOperatorIntegral μ F hm C hb := by
  ext x
  change (∫ s, F s (T x) ∂μ) = T (∫ s, F s x ∂μ)
  rw [← T.integral_comp_comm (integrable_bounded_operator_vector μ F hm hb x)]
  apply integral_congr_ae
  filter_upwards [hT] with s hs
  exact congrArg (fun A : H →L[ℂ] H => A x) hs

/-- Von Neumann algebra membership is retained without any norm
measurability hypothesis on the field. -/
theorem probabilityOperatorIntegral_mem (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (M : VonNeumannAlgebra H)
    (hM : ∀ᵐ s ∂μ, F s ∈ M) : probabilityOperatorIntegral μ F hm C hb ∈ M := by
  change probabilityOperatorIntegral μ F hm C hb ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro T hT
  apply (probabilityOperatorIntegral_commutes μ F hm C hb T ?_).symm
  filter_upwards [hM] with s hs
  exact hT (F s) hs

end

end KadisonKastler

end OAI
