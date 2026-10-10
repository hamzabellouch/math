import OAI.Geometry.RCD.Coordinates.RegularLimitBallBounds
import OAI.Geometry.RCD.Metric.InteriorBallMassIdentification

namespace OAI

/-! # Exact interior ball masses in the actual regular metric limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {K : ℝ} {n : ℕ}

theorem NoncollapsedRCD.regular_limit_ball_mass
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {o : X} (ho : IsRegular n o)
    {q z : Y} {S t : ℝ} (hS : 0 < S) (ht : 0 < t) (hroom : dist z q+t < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (hfin : ∀ k, hausdorff n X (ball (p k) (S*r k)) ≠ ⊤)
    {Q : ProbabilityMeasure Y}
    (hlim : Tendsto (fun k => metricBallLaw (hausdorff n X)
      (p k) (r k) S (V k) (hfin k)) atTop (𝓝 Q)) :
    (Q : Measure Y).real (ball z t) = (t/S)^n ∧
      (Q : Measure Y).real (closedBall z t) = (t/S)^n := by
  apply interior_ball_mass_identification (Q : Measure Y) z n hS ht
    (show t < S-dist z q by linarith)
  intro a s b ha has hsb hb
  exact hX.regular_limit_ball_bounds hn ho hS ha has hsb (by linarith)
    p r ε V hp hr hr0 hε hVm hV hfin hlim

end RegularPointCoordinates

end

end OAI
