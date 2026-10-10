import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # A weak Laplacian tested where its potential has bounded gradient

Only the gradient on the nonzero set of the test is needed. The test's
gradient vanishes on its zero level set by Sobolev locality.
-/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem weak_source_test_gradient_bound
    (w φ : SobolevSpace μ Q) (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ Q w q)
    {L : ℝ}
    (hgrad : ∀ᵐ x ∂μ, SobolevSpace.toLp μ Q φ x ≠ 0 → SobolevSpace.minimalSlope μ Q w x ≤ L)
    (hi : Integrable (SobolevSpace.minimalSlope μ Q φ) μ) :
    |inner ℝ q (SobolevSpace.toLp μ Q φ)| ≤ L * ∫ x, SobolevSpace.minimalSlope μ Q φ x ∂μ := by
  calc
    _ = |energyForm μ Q w φ| := by rw [hq φ,abs_neg]
    _ ≤ inner ℝ (SobolevSpace.minimalSlope μ Q w) (SobolevSpace.minimalSlope μ Q φ) :=
      energyForm_abs_le_slope_inner μ Q w φ
    _ = ∫ x, SobolevSpace.minimalSlope μ Q w x * SobolevSpace.minimalSlope μ Q φ x ∂μ := by
      rw [L2.inner_def]
      simp only [Real.inner_apply]
    _ ≤ ∫ x, L * SobolevSpace.minimalSlope μ Q φ x ∂μ := by
      apply integral_mono_ae ((Lp.memLp _).integrable_mul (Lp.memLp _)) (hi.const_mul L)
      filter_upwards [hgrad,SobolevSpace.minimalSlope_zero_on_zero μ Q φ,
        (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q φ)] with x hx hz hp
      by_cases hφ : SobolevSpace.toLp μ Q φ x = 0
      · simp only [Pi.mul_apply,hz hφ,mul_zero,le_refl]
      · exact mul_le_mul_of_nonneg_right (hx hφ) hp
    _ = _ := integral_const_mul _ _

end RegularPointCoordinates

end

end OAI
