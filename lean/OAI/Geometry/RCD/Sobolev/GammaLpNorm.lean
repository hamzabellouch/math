import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # L² size of an energy density with bounded gradient -/

open MeasureTheory
open scoped NNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem gammaLp_norm_le (f g : SobolevSpace μ hQ) (L : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L)
    (hΓ : MemLp (localGamma μ hQ f g) 2 μ) :
    ‖hΓ.toLp (localGamma μ hQ f g)‖ ≤ (L : ℝ) * ‖g‖ := by
  have hh : ‖hΓ.toLp (localGamma μ hQ f g)‖ ≤
      (L : ℝ) * ‖SobolevSpace.minimalSlope μ hQ g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hΓ.coeFn_toLp, hf, localGamma_abs_le μ hQ f g,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ g)]
      with x hx hfx hΓx h0
    simpa only [hx, Real.norm_eq_abs, abs_of_nonneg h0] using
      hΓx.trans (mul_le_mul_of_nonneg_right hfx h0)
  exact hh.trans (mul_le_mul_of_nonneg_left (SobolevSpace.minimalSlope_norm_le μ hQ g)
    L.coe_nonneg)

end RegularPointCoordinates

end OAI
