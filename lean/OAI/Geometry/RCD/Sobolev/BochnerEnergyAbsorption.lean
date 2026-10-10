import OAI.Geometry.RCD.Sobolev.BochnerMixedRecovery
import OAI.Geometry.RCD.Sobolev.WeightedGammaGradientBound

namespace OAI

/-! # Energy-density bounds depending only on the L² Laplacian -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem weakLaplacian_mixed_lower_L2 (f d w : SobolevSpace μ hQ) (C L : ℝ≥0)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L)
    (hΔ : IsWeakLaplacian μ hQ f (SobolevSpace.toLp μ hQ d)) :
    -((C : ℝ) * ‖SobolevSpace.toLp μ hQ d‖ ^ 2) -
        (L : ℝ) * ‖SobolevSpace.toLp μ hQ d‖ * ‖SobolevSpace.minimalSlope μ hQ w‖ ≤
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f d := by
  have he := weakLaplacian_mixed_identity_L2 μ hQ f d w C L hw hf hΔ
  have hmix := weightedGamma_le_of_bounded_gradient μ hQ (SobolevSpace.toLp μ hQ d) f w L hf
  have hwi : ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ w x‖ ≤ (C : ℝ) := by
    simpa only [Real.norm_eq_abs] using hw
  have hdi : Integrable (fun x => (SobolevSpace.toLp μ hQ d x) ^ 2) μ :=
    (Lp.memLp (SobolevSpace.toLp μ hQ d)).integrable_sq
  have hmass : (∫ x, SobolevSpace.toLp μ hQ w x * (SobolevSpace.toLp μ hQ d x) ^ 2 ∂μ) ≤
      (C : ℝ) * ‖SobolevSpace.toLp μ hQ d‖ ^ 2 := by
    rw [← integral_sq_Lp, ← integral_const_mul]
    apply integral_mono_ae
      (hdi.bdd_mul (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ w)) hwi) (hdi.const_mul C)
    filter_upwards [hw] with x hx
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans hx) (sq_nonneg _)
  linarith [(le_abs_self (weightedGamma μ hQ (SobolevSpace.toLp μ hQ d) f w)).trans hmix]

theorem bochner_energy_absorption (f d G : SobolevSpace μ hQ) (C L : ℝ≥0) (K : ℝ)
    (hG : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ G x| ≤ C)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L)
    (hΔ : IsWeakLaplacian μ hQ f (SobolevSpace.toLp μ hQ d))
    (hB : energyForm μ hQ G G + 2 * K * ‖SobolevSpace.toLp μ hQ G‖ ^ 2 +
      2 * weightedGamma μ hQ (SobolevSpace.toLp μ hQ G) f d ≤ 0) :
    energyForm μ hQ G G ≤ 4 * |K| * ‖SobolevSpace.toLp μ hQ G‖ ^ 2 +
      4 * ((C : ℝ) + (L : ℝ) ^ 2) * ‖SobolevSpace.toLp μ hQ d‖ ^ 2 := by
  have hm := weakLaplacian_mixed_lower_L2 μ hQ f d G C L hG hf hΔ
  have he : ‖SobolevSpace.minimalSlope μ hQ G‖ ^ 2 = energyForm μ hQ G G := by
    rw [SobolevSpace.minimalSlope_norm_sq, energyForm_self]
  have hK := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg ‖SobolevSpace.toLp μ hQ G‖)
  nlinarith [sq_nonneg (‖SobolevSpace.minimalSlope μ hQ G‖ -
    2 * (L : ℝ) * ‖SobolevSpace.toLp μ hQ d‖)]

end RegularPointCoordinates

end

end OAI
