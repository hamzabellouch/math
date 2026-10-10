import OAI.Geometry.RCD.Sobolev.BoundedPowerPairContinuity
import OAI.Geometry.RCD.Heat.BoundedHeatOrder

namespace OAI

/-! # Continuous power means including the original heat endpoints -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)

def boundedHeatPowerMean (f g : Lp ℝ 2 μ) (A B : ℝ≥0) (n : ℕ) (c t : ℝ) : ℝ :=
  boundedPowerPair μ A B n (heatAt μ Q (c*t) f) (heatAt μ Q (c*(1-t)) g)

theorem boundedHeatPowerMean_continuous (f g : Lp ℝ 2 μ) (A B : ℝ≥0) (n : ℕ) (c : ℝ) :
    Continuous (boundedHeatPowerMean μ Q f g A B n c) :=
  (boundedPowerPair_continuous μ A B n).comp
    (((heatAt_continuous μ Q f).comp (continuous_const.mul continuous_id)).prodMk
      ((heatAt_continuous μ Q g).comp (continuous_const.mul (continuous_const.sub continuous_id))))

theorem boundedHeatPowerMean_eq_integral (f g : Lp ℝ 2 μ) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ A) (hg : ∀ᵐ x ∂μ, |g x| ≤ B) (n : ℕ) (c t : ℝ) :
    boundedHeatPowerMean μ Q f g A B n c t =
    ∫ x, (heatAt μ Q (c*t) f x*heatAt μ Q (c*(1-t)) g x)^(n+1) ∂μ :=
  boundedPowerPair_eq_integral μ A B n _ _
    (heatAt_abs_le_const μ Q _ A f hf) (heatAt_abs_le_const μ Q _ B g hg)

end RegularPointCoordinates

end

end OAI
