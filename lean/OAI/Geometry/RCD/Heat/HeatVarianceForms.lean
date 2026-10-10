import OAI.Geometry.RCD.Heat.HeatVarianceLower

namespace OAI

/-! # Continuity of the forms in the reverse Poincaré inequality -/

open MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

/-- Weighted energy of a positive-time heat flow is continuous in its
initial L² data. -/
theorem heat_weighted_energy_continuous (w : Lp ℝ 2 μ) (B : ℝ≥0)
    (hw : ∀ᵐ x ∂μ, |w x| ≤ B) (T : ℝ) (hT : 0 < T) :
    Continuous (fun f : Lp ℝ 2 μ => ∫ x, w x*(SobolevSpace.minimalSlope μ hQ
      (heatSobolev μ hQ T hT f) x)^2 ∂μ) := by
  have hc := lp_weighted_square_continuous μ (Lp.aestronglyMeasurable w)
    (by simpa only [Real.norm_eq_abs] using hw)
  exact hc.comp ((SobolevSpace.minimalSlope_lipschitz μ hQ).continuous.comp
    (heatSobolevMap μ hQ T hT).continuous)

/-- Both terms of the heat variance are continuous in L². -/
theorem heat_variance_continuous (w : Lp ℝ 2 μ) (B : ℝ≥0)
    (hw : ∀ᵐ x ∂μ, |w x| ≤ B) (T : ℝ) :
    Continuous (fun f : Lp ℝ 2 μ =>
      (∫ x, heatAt μ hQ T w x*(f x)^2 ∂μ)-
        (∫ x, w x*(heatAt μ hQ T f x)^2 ∂μ)) := by
  have hwc := lp_weighted_square_continuous μ (Lp.aestronglyMeasurable w)
    (by simpa only [Real.norm_eq_abs] using hw)
  have hTw := heatAt_abs_le_const μ hQ T B w hw
  have hTwh := lp_weighted_square_continuous μ (Lp.aestronglyMeasurable (heatAt μ hQ T w))
    (by simpa only [Real.norm_eq_abs] using hTw)
  exact hTwh.sub (hwc.comp (heatAt μ hQ T).continuous)

end RegularPointCoordinates

end

end OAI
