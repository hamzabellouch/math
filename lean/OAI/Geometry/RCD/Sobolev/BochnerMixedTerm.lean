import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Integrating the mixed term in weak Bochner

Testing the weak Laplacian against the product of its derivative and a
bounded Sobolev weight moves the mixed term onto the weight. This is the
identity needed for an energy bound depending only on the L² Laplacian.
-/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem weakLaplacian_mixed_weight_identity (f d w : SobolevSpace μ hQ)
    (A C : ℝ≥0)
    (hd : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ d x| ≤ A)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C)
    (hΔ : IsWeakLaplacian μ hQ f (SobolevSpace.toLp μ hQ d)) :
    weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f d +
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ d) f w =
        -(∫ x, SobolevSpace.toLp μ hQ w x * (SobolevSpace.toLp μ hQ d x) ^ 2 ∂μ) := by
  have hdn : ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ d x‖ ≤ (A : ℝ) := by
    simpa only [Real.norm_eq_abs] using hd
  have hwn : ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ w x‖ ≤ (C : ℝ) := by
    simpa only [Real.norm_eq_abs] using hw
  have hi₁ := (localGamma_memL1 μ hQ f d).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ w)) hwn
  have hi₂ := (localGamma_memL1 μ hQ f w).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ d)) hdn
  have htest := hΔ (SobolevSpace.product μ hQ d w A C)
  have hleft : energyForm μ hQ f (SobolevSpace.product μ hQ d w A C) =
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f d +
        weightedGamma μ hQ (SobolevSpace.toLp μ hQ d) f w := by
    rw [← integral_localGamma_eq_energyForm]
    unfold weightedGamma
    rw [← integral_add hi₁ hi₂]
    apply integral_congr_ae
    filter_upwards [localGamma_product_right μ hQ f d w A C hd hw] with x hx
    rw [hx]
    ring
  have hright : inner ℝ (SobolevSpace.toLp μ hQ d)
      (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ d w A C)) =
      ∫ x, SobolevSpace.toLp μ hQ w x * (SobolevSpace.toLp μ hQ d x) ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ d w A C hd hw] with x hx
    simp only [Real.inner_apply, hx]
    ring
  rw [hleft, hright] at htest
  exact htest

end RegularPointCoordinates

end

end OAI
