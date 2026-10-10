import OAI.Geometry.RCD.Metric.PointedMetricInteriorLift

namespace OAI

/-! # Interior lifts with bounds at every sequence index -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pointed_bounded_lift {q y : Y} {S T : ℝ}
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (hTS : T < S) (hy : dist y q < T) :
    ∃ x : ℕ → X, (∀ k, dist (x k) (p k) ≤ T * r k) ∧
      Tendsto (fun k => V k (x k)) atTop (𝓝 y) := by
  classical
  obtain ⟨x,hx,hVx⟩ := pointed_metric_interior_lift p r ε V hr hε hV hTS hy
  let x' k := if dist (x k) (p k) ≤ T * r k then x k else p k
  refine ⟨x',?_,?_⟩
  · intro k
    dsimp only [x']
    split_ifs with hk
    · exact hk
    · rw [dist_self]
      exact mul_nonneg (lt_of_le_of_lt dist_nonneg hy).le (hr k).le
  · apply hVx.congr'
    filter_upwards [hx] with k hk
    simp only [x',ite_eq_left hk]

end RegularPointCoordinates

end

end OAI
