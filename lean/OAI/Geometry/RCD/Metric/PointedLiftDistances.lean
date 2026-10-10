import OAI.Geometry.RCD.Metric.PointedMetricInteriorLift

namespace OAI

/-! # Distances of convergent lifts in the prescribed physical scales -/

open Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pointed_lift_distance_tendsto {q y z : Y} {S : ℝ}
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (x x' : ℕ → X)
    (hx : ∀ᶠ k in atTop, dist (x k) (p k)≤S*r k)
    (hx' : ∀ᶠ k in atTop, dist (x' k) (p k)≤S*r k)
    (hy : Tendsto (fun k => V k (x k)) atTop (𝓝 y))
    (hz : Tendsto (fun k => V k (x' k)) atTop (𝓝 z)) :
    Tendsto (fun k => dist (x k) (x' k)/r k) atTop (𝓝 (dist y z)) := by
  apply (hy.dist hz).congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ hε0
  filter_upwards [hx,hx'] with k hk hk'
  rw [Real.dist_eq]
  exact (hV k).2.1 _ _ hk hk'

end RegularPointCoordinates

end

end OAI
