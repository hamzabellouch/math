import OAI.Geometry.RCD.Metric.PositiveSquaredDistance
import OAI.Geometry.RCD.Metric.InwardLocality
import OAI.Geometry.RCD.Metric.DyadicDistanceSources

namespace OAI

/-! # The radial derivative does not depend on the outer distance cutoff -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- All positive squared-distance data at one center agree locally.
Consequently their pairing with an arbitrary Sobolev direction is the same
raw radial derivative, even though their compact supports differ. -/
theorem positiveSquaredDistance_pairing_independent {p : X} {r R₁ R₂ C₁ C₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (hr₁ : r ≤ R₁) (hr₂ : r ≤ R₂)
    (χ₁ : GoodLaplacianCutoff μ hQ p R₁ C₁)
    (χ₂ : GoodLaplacianCutoff μ hQ p R₂ C₂) (a : SobolevSpace μ hQ) :
    localGamma μ hQ (positiveSquaredDistance μ hQ hR₁ χ₁) a =ᵐ[μ.restrict (ball p r)]
      localGamma μ hQ (positiveSquaredDistance μ hQ hR₂ χ₂) a := by
  apply localGamma_eq_of_constant_difference μ hQ (ball p r) _ _ a 0
  filter_upwards [ae_restrict_of_ae (positiveSquaredDistance_representative μ hQ hR₁ χ₁),
    ae_restrict_of_ae (positiveSquaredDistance_representative μ hQ hR₂ χ₂),
    ae_restrict_of_ae (Lp.coeFn_sub
      (SobolevSpace.toLp μ hQ (positiveSquaredDistance μ hQ hR₁ χ₁))
      (SobolevSpace.toLp μ hQ (positiveSquaredDistance μ hQ hR₂ χ₂))),
    ae_restrict_mem measurableSet_ball] with x h₁ h₂ hsub hx
  change (SobolevSpace.toLp μ hQ (positiveSquaredDistance μ hQ hR₁ χ₁) -
    SobolevSpace.toLp μ hQ (positiveSquaredDistance μ hQ hR₂ χ₂)) x = 0
  rw [hsub, Pi.sub_apply, h₁, h₂,
    positiveSquaredDistanceValue_on_ball μ hQ χ₁ ((ball_subset_ball hr₁) hx),
    positiveSquaredDistanceValue_on_ball μ hQ χ₂ ((ball_subset_ball hr₂) hx), sub_self]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [IsFiniteMeasureOnCompacts μ] in
theorem distanceSourceRadius_add (r0 : ℝ) (i m : ℕ) :
    distanceSourceRadius r0 (i + m) = distanceSourceRadius r0 i / (2 : ℝ) ^ m := by
  unfold distanceSourceRadius
  rw [show i + m + 1 = (i + 1) + m by omega, pow_add]
  ring

end RegularPointCoordinates

end

end OAI
