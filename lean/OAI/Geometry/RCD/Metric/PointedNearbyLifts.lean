import OAI.Geometry.RCD.Metric.PointedLiftDistances

namespace OAI

/-! # Approximate endpoints preserve convergence under the prescribed maps -/

open Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pointed_nearby_lift_tendsto {q y : Y} {S : ℝ}
    (p x x' : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (hx : ∀ᶠ k in atTop, dist (x k) (p k) ≤ S * r k)
    (hx' : ∀ᶠ k in atTop, dist (x' k) (p k) ≤ S * r k)
    (hxy : Tendsto (fun k => dist (x k) (x' k)/r k) atTop (𝓝 0))
    (hy : Tendsto (fun k => V k (x k)) atTop (𝓝 y)) :
    Tendsto (fun k => V k (x' k)) atTop (𝓝 y) := by
  apply hy.congr_dist
  have hsum : Tendsto (fun k => dist (x k) (x' k)/r k + ε k) atTop (𝓝 0) := by
    simpa only [zero_add] using hxy.add hε
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ hsum
  filter_upwards [hx,hx'] with k hk hk'
  have hh := (abs_le.mp ((hV k).2.1 _ _ hk hk')).2
  linarith

end RegularPointCoordinates

end

end OAI
