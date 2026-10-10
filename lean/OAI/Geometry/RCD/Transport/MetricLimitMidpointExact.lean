import OAI.Geometry.RCD.Transport.MetricLimitMidpointContraction
import OAI.Geometry.RCD.Metric.ClosedBallMassLimit

namespace OAI

/-! # Exact closed target in the limiting midpoint inequality -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_limit_midpoint_exact {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {S ρ η a b : ℝ} (hS : 0 < S) (hρ : 0 ≤ ρ) (hρS : ρ < S)
    (x y z : Euclidean n) (hxa : ‖x‖+a < ρ) (hyb : ‖y‖+b < ρ)
    (hx : closedBall x a ⊆ closedBall z η) (hy : closedBall y b ⊆ closedBall z η)
    (hroom : ρ+2*η < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -ε k ≤ K*(r k)^2) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hfin : ∀ k, hausdorff n X (ball (p k) (S*r k)) ≠ ⊤)
    {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto (fun k => normalizedBallPushforward (hausdorff n X)
      (p k) (r k) S (V k) (hfin k)) atTop (𝓝 Q))
    (hAx : 0 < (Q : Measure (Euclidean n)).real (ball x a))
    (hBy : 0 < (Q : Measure (Euclidean n)).real (ball y b)) :
    (1/2:ℝ)^n*(Q : Measure (Euclidean n)).real (ball y b) ≤
      (Q : Measure (Euclidean n)).real (closedBall ((1/2:ℝ) • (x+y)) ((a+b)/2)) := by
  apply finite_measure_closedBall_of_enlargements (Q : Measure (Euclidean n))
  intro κ hκ
  exact hX.metric_limit_midpoint_enlarged hn hK hS hρ hρS hκ x y z hxa hyb hx hy
    hroom p r ε V hr hε hcurv hVm hV hfin hlim hAx hBy

end RegularPointCoordinates

end

end OAI
