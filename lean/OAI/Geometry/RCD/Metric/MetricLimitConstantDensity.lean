import OAI.Geometry.RCD.Metric.MetricLimitLocalDensity
import OAI.Geometry.RCD.Metric.LocalDensityGluing

namespace OAI

/-! # One constant density on the whole open Euclidean limit ball -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_limit_constant_density {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {S : ℝ} (hS : 0 < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -ε k ≤ K*(r k)^2) (hVm : ∀ k, Measurable (V k))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hfin : ∀ k, hausdorff n X (ball (p k) (S*r k)) ≠ ⊤)
    {Q : ProbabilityMeasure (Euclidean n)}
    (hlim : Tendsto (fun k => normalizedBallPushforward (hausdorff n X)
      (p k) (r k) S (V k) (hfin k)) atTop (𝓝 Q))
    (hpositive : ∀ x ∈ ball (0 : Euclidean n) S, ∀ t : ℝ, 0 < t →
      0 < (Q : Measure (Euclidean n)).real (ball x t)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x ∂volume.restrict (ball (0 : Euclidean n) S),
      (((Q : Measure (Euclidean n)).restrict (ball 0 S)).rnDeriv volume x).toReal=c := by
  apply ae_constant_on_ball_of_locally_constant hS
  exact hX.metric_limit_local_density hn hK hS p r ε V hr hε hcurv hVm hV hfin hlim hpositive

end RegularPointCoordinates

end

end OAI
