import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedRieszInterior

namespace OAI

/-!
# Integrable errors for capped interior Riesz kernels

The capped interior integrand is integrable for finite measures and bounded
continuous tests. For Lipschitz tests, a near-diagonal weight dominates its
difference from the original integrand, giving integrability of the latter
and quantitative control of the capping error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem cappedRieszInterior_integrable {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (e : Ambient d) (φ : Ambient d → ℝ) (hφ : Continuous φ)
    (B : ℝ≥0) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    Integrable (cappedRieszInterior m ε e φ) (μ.prod μ) := by
  apply Integrable.of_bound
    (cappedRieszInterior_continuous m ε hε e φ hφ).measurable.aestronglyMeasurable
    ((2 * (B : ℝ) * ‖e‖) * (ε ^ m)⁻¹)
  exact Eventually.of_forall fun q => by
    simpa only [Real.norm_eq_abs] using! cappedRieszInterior_bound m ε hε e φ B hB q

theorem rieszInterior_integrable_and_cap_error {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    Integrable (rieszInteriorIntegrand (p + 1) e φ) (μ.prod μ) ∧
      |(∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂μ.prod μ) -
        ∫ q, cappedRieszInterior (p + 1) ε e φ q ∂μ.prod μ| ≤
          (‖e‖ * (L : ℝ)) * (μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * ε))) := by
  let F := rieszInteriorIntegrand (p + 1) e φ
  let G := cappedRieszInterior (p + 1) ε e φ
  have hG : Integrable G (μ.prod μ) :=
    cappedRieszInterior_integrable (p + 1) ε hε μ e φ hφ.continuous B hB
  have hFm : Measurable F := by
    have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
    have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
    have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
    have hφm := hφ.continuous.measurable
    dsimp only [F]
    unfold rieszInteriorIntegrand kernel
    fun_prop
  have hdom := (nearPairWeight_integrable p C μ hg ε hε).const_mul (‖e‖ * (L : ℝ))
  have herr : Integrable (fun q => F q - G q) (μ.prod μ) := by
    apply hdom.mono' (hFm.aestronglyMeasurable.sub hG.aestronglyMeasurable)
    exact Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using! rieszInterior_cap_error_pointwise p ε e φ L hφ q
  have hF : Integrable F (μ.prod μ) := by
    have heq : F = fun q => (F q - G q) + G q := by funext q; ring
    rw [heq]
    exact herr.add hG
  refine ⟨hF, ?_⟩
  change |(∫ q, F q ∂μ.prod μ) - ∫ q, G q ∂μ.prod μ| ≤ _
  rw [← integral_sub hF hG]
  calc
    _ ≤ ∫ q, |F q - G q| ∂μ.prod μ := abs_integral_le_integral_abs
    _ ≤ ∫ q, (‖e‖ * (L : ℝ)) * nearPairWeight p ε q ∂μ.prod μ :=
      integral_mono_ae herr.abs hdom
        (Eventually.of_forall fun q => rieszInterior_cap_error_pointwise p ε e φ L hφ q)
    _ = (‖e‖ * (L : ℝ)) * ∫ q, nearPairWeight p ε q ∂μ.prod μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (nearPairWeight_integral_bound p C μ hg ε hε)
      (mul_nonneg (norm_nonneg _) L.coe_nonneg)

end

end RieszRectifiability

end OAI
