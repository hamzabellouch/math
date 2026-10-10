import OAI.Geometry.RCD.Metric.MetricLimitIsodiametric
import OAI.Geometry.RCD.Coordinates.HausdorffLowerNormalization
import OAI.Geometry.RCD.Coordinates.HausdorffUpperNormalization

namespace OAI

/-! # Exact Euclidean Hausdorff normalization from the actual RCD limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.metric_limit_hausdorff_normalization {K : ℝ} {n : ℕ}
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
    hausdorff n (Euclidean n) = volume := by
  have hn0 : 0 < n := by omega
  have hl := hX.metric_limit_isodiametric hn hK (a := S/4) (by positivity)
    (by linarith only [hS]) p r ε V hr hε hcurv hVm hV hfin hlim hpositive
  exact le_antisymm (normalized_hausdorff_le_volume hn0)
    (volume_le_normalized_hausdorff_of_isodiametric hn0
      (compact_isodiametric_of_local (by positivity : 0 < S/4) hl))

end RegularPointCoordinates

end

end OAI
