import OAI.Geometry.RCD.Heat.SourceTimeIntegrability

namespace OAI

/-! # Exact average-to-point comparison with one signed source difference -/

open Set MeasureTheory Filter
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The exact semigroup comparison, with the long-time difference inside
one integral. Both source integrals are genuinely integrable. -/
theorem IsMeasureLaplacian.average_initial_sub_point_heat_difference
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : X) :
    (μ.real A)⁻¹ * (∫ z in A, SobolevSpace.toLp μ hQ u z ∂μ) -
      kernelHeat μ hQ hk s (SobolevSpace.toLp μ hQ u) x =
      ((μ.real A)⁻¹ * (∫ z in A, heatAt μ hQ t (SobolevSpace.toLp μ hQ u) z ∂μ) -
        kernelHeat μ hQ hk t (SobolevSpace.toLp μ hQ u) x) -
      (∫ r in 0..s, (∫ᵛ z, kernelAverage μ ker r A z ∂<•ν)) -
      (∫ r in s..t, ((∫ᵛ z, kernelAverage μ ker r A z ∂<•ν) -
        (∫ᵛ z, ker r x z ∂<•ν))) := by
  have ha := hν.average_source_intervalIntegrable μ hQ hk c hR hu hsν A hA hAt hs.le hst
  have hp := hν.point_source_intervalIntegrable μ hQ hk c hR hu hsν hs hst x
  rw [intervalIntegral.integral_sub ha hp]
  have he := hν.average_initial_sub_point_heat μ hQ hk c hR hu hsν A hA hAt hs hst x
  linarith only [he]

end RegularPointCoordinates

end

end OAI
