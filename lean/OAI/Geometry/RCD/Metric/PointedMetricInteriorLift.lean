import OAI.Geometry.RCD.Metric.PointedApproximationLifts

namespace OAI

/-! # Interior lifts through the same pointed metric approximation maps -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pointed_metric_interior_lift {q y : Y} {S T : ℝ}
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0<r k) (hε0 : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k))
    (hTS : T<S) (hy : dist y q<T) :
    ∃ x : ℕ → X,
      (∀ᶠ k in atTop, dist (x k) (p k)≤T*r k) ∧
      Tendsto (fun k => V k (x k)) atTop (𝓝 y) := by
  classical
  have hS : 0<S := lt_of_le_of_lt dist_nonneg (hy.trans hTS)
  have hex (k : ℕ) : ∃ x : X, dist y q≤S-ε k →
      dist x (p k)≤S*r k ∧ dist (V k x) y≤ε k := by
    by_cases hh : dist y q≤S-ε k
    · obtain ⟨x,hx,hxy⟩ := (hV k).2.2 y hh
      exact ⟨x,fun _ => ⟨hx,hxy⟩⟩
    · exact ⟨p k,fun hc => (hh hc).elim⟩
  choose x hx using hex
  have hroom : ∀ᶠ k in atTop, dist y q≤S-ε k ∧ dist y q+3*ε k≤T := by
    filter_upwards [hε0.eventually (gt_mem_nhds (sub_pos.mpr (hy.trans hTS))),
      hε0.eventually (gt_mem_nhds (show 0<(T-dist y q)/3 by linarith))] with k hk hkt
    constructor <;> linarith
  refine ⟨x,?_,?_⟩
  · filter_upwards [hroom] with k hk
    obtain ⟨hxs,hxy⟩ := hx k hk.1
    have hp : dist (p k) (p k)≤S*r k := by
      simp only [dist_self]
      exact mul_nonneg hS.le (hr k).le
    have hd := (abs_le.mp ((hV k).2.1 (x k) (p k) hxs hp)).1
    have ht := dist_triangle4 (V k (x k)) y q (V k (p k))
    rw [dist_comm q (V k (p k))] at ht
    apply (div_le_iff₀ (hr k)).mp
    linarith [(hV k).1,hk.2]
  · apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [hroom,hε0.eventually (gt_mem_nhds hδ)] with k hk hsmall
    exact ((hx k hk.1).2).trans_lt hsmall

end RegularPointCoordinates

end

end OAI
