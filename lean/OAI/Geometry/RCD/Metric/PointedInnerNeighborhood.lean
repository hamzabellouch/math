import OAI.Geometry.RCD.Metric.PointedMetricInteriorLift

namespace OAI

/-! # An interior limit point has a uniform physical neighborhood inside the image ball -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pointed_inner_neighborhood {q y : Y}
    (p z : ℕ → X) (r δ : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0<r k) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (δ k) (V k))
    (hz : ∀ᶠ k in atTop, dist (z k) (p k)≤r k/128)
    (hVy : Tendsto (fun k => V k (z k)) atTop (𝓝 y))
    (hy : dist y q<1/256) :
    ∃ c : ℝ, 0<c ∧ c≤1/128 ∧ ∀ᶠ k in atTop,
      dist (z k) (p k)≤5*r k ∧ ∀ x∈ball (z k) (c*r k/48),
        dist x (p k)≤5*r k ∧ V k x∈closedBall q (1/256) := by
  let c : ℝ := 1/256-dist y q
  have hc : 0<c := sub_pos.mpr hy
  have hc1 : c≤1/128 := by dsimp [c]; linarith [dist_nonneg (x:=y) (y:=q)]
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [hz,hδ0.eventually (gt_mem_nhds (show 0<c/4 by positivity)),
    Metric.tendsto_nhds.mp hVy (c/4) (by positivity)] with k hzk hδk hVzk
  have hrk := hr k
  have hz5 : dist (z k) (p k)≤5*r k := by linarith
  refine ⟨hz5,?_⟩
  intro x hx
  change dist x (z k)<c*r k/48 at hx
  have hcr : c*r k≤r k/128 := by nlinarith [mul_le_mul_of_nonneg_right hc1 hrk.le]
  have hx5 : dist x (p k)≤5*r k := by linarith [dist_triangle x (z k) (p k)]
  refine ⟨hx5,?_⟩
  have hd := (abs_le.mp ((hV k).2.1 x (z k) hx5 hz5)).2
  have hnorm : dist x (z k)/r k<c/48 := (div_lt_iff₀ hrk).mpr (by nlinarith [hx])
  change dist (V k x) q≤1/256
  have ht := dist_triangle4 (V k x) (V k (z k)) y q
  dsimp [c] at *
  linarith

end RegularPointCoordinates

end

end OAI
