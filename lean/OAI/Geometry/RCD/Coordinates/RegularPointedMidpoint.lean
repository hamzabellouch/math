import OAI.Geometry.RCD.Coordinates.RegularNearbyMidpoints
import OAI.Geometry.RCD.Transport.QuadraticMidpointLimit
import OAI.Geometry.RCD.Metric.PointedNearbyLifts

namespace OAI

/-! # Actual near-regular midpoint identities in an arbitrary proper metric limit -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [MetricSpace Y] [ProperSpace Y] {K : ℝ} {n : ℕ}
  (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]

include hX in
theorem regular_pointed_midpoint (hn : 2 ≤ n) (hK : K ≤ 0)
    {o : X} (ho : IsRegular n o) {q a b : Y} (w : ℕ → Y)
    (p x y : ℕ → X) (z : ℕ → ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K * (4 * r k)^2)
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k))
    (hx : ∀ k, dist (x k) (p k) ≤ r k/2)
    (hy : ∀ k, dist (y k) (p k) ≤ r k/2)
    (hz : ∀ i k, dist (z i k) (p k) ≤ r k)
    (hVx : Tendsto (fun k => V k (x k)) atTop (𝓝 a))
    (hVy : Tendsto (fun k => V k (y k)) atTop (𝓝 b))
    (hVz : ∀ i, Tendsto (fun k => V k (z i k)) atTop (𝓝 (w i))) :
    ∃ c : Y, dist c q ≤ 4 ∧ dist a c = dist a b/2 ∧ dist c b = dist a b/2 ∧
      ∀ i, dist (w i) c^2 = (dist (w i) a^2+dist (w i) b^2)/2-dist a b^2/4 := by
  classical
  have hzo i : Tendsto (z i) atTop (𝓝 o) := by
    apply hp.congr_dist
    apply squeeze_zero (fun _ => dist_nonneg) _ hr0
    intro k
    simpa only [dist_comm] using hz i k
  obtain ⟨η,γ,hη,hγ,hquad⟩ := hX.regular_nearby_midpoints hn hK ho p x y z r hp hzo hr hr0
    hcurv hx hy hz
  have hg k := (hγ k).2.1
  have hstay k (t : Time) : dist (γ k t) (p k) ≤ 5 * r k :=
    ((hγ k).2.2.2.2 t).trans (by nlinarith [hr k])
  have hxS k : dist (x k) (p k) ≤ 5 * r k := (hx k).trans (by nlinarith [hr k])
  have hyS k : dist (y k) (p k) ≤ 5 * r k := (hy k).trans (by nlinarith [hr k])
  have hnear0 : Tendsto (fun k => dist (x k) (γ k 0)/r k) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => div_nonneg dist_nonneg (hr k).le) _ hη
    intro k
    apply (div_le_iff₀ (hr k)).mpr
    simpa only [dist_comm] using (hγ k).2.2.1.le
  have hnear1 : Tendsto (fun k => dist (y k) (γ k 1)/r k) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => div_nonneg dist_nonneg (hr k).le) _ hη
    intro k
    apply (div_le_iff₀ (hr k)).mpr
    simpa only [dist_comm] using (hγ k).2.2.2.1.le
  have h0 := pointed_nearby_lift_tendsto p x (fun k => γ k 0) r ε V hε hV
    (Eventually.of_forall hxS) (Eventually.of_forall (fun k => hstay k 0)) hnear0 hVx
  have h1 := pointed_nearby_lift_tendsto p y (fun k => γ k 1) r ε V hε hV
    (Eventually.of_forall hyS) (Eventually.of_forall (fun k => hstay k 1)) hnear1 hVy
  let m k := γ k quadraticMidpointTime
  have hbound k (hk : ε k ≤ 1/2) : dist (V k (m k)) q ≤ 4 := by
    have hpS : dist (p k) (p k) ≤ 5*r k := by
      rw [dist_self]
      exact mul_nonneg (by norm_num) (hr k).le
    have hh := (abs_le.mp ((hV k).2.1 (m k) (p k) (hstay k _) hpS)).2
    have ht := dist_triangle (V k (m k)) (V k (p k)) q
    have hrb : dist (m k) (p k)/r k ≤ 3 :=
      (div_le_iff₀ (hr k)).mpr ((hγ k).2.2.2.2 _)
    linarith [(hV k).1]
  let v k := if ε k ≤ 1/2 then V k (m k) else q
  have hv k : v k ∈ closedBall q 4 := by
    dsimp only [v]
    split_ifs with hk
    · exact hbound k hk
    · simp
  obtain ⟨c,hc,α,hα,hlim⟩ := (isCompact_closedBall q (4:ℝ)).tendsto_subseq hv
  have hm : Tendsto (fun k => V (α k) (m (α k))) atTop (𝓝 c) := by
    apply hlim.congr'
    filter_upwards [hα.tendsto_atTop.eventually
      (hε.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))] with k hk
    exact ite_eq_left hk.le
  have h01 := pointed_lift_distance_tendsto p r ε V hε hV
    (fun k => γ k 0) (fun k => γ k 1)
    (Eventually.of_forall (fun k => hstay k 0)) (Eventually.of_forall (fun k => hstay k 1)) h0 h1
  have h0m := pointed_lift_distance_tendsto (p∘α) (r∘α) (ε∘α) (V∘α)
    (hε.comp hα.tendsto_atTop) (fun k => hV (α k)) (fun k => γ (α k) 0) (m∘α)
    (Eventually.of_forall (fun k => hstay (α k) 0))
    (Eventually.of_forall (fun k => hstay (α k) _)) (h0.comp hα.tendsto_atTop) hm
  have hm1 := pointed_lift_distance_tendsto (p∘α) (r∘α) (ε∘α) (V∘α)
    (hε.comp hα.tendsto_atTop) (fun k => hV (α k)) (m∘α) (fun k => γ (α k) 1)
    (Eventually.of_forall (fun k => hstay (α k) _))
    (Eventually.of_forall (fun k => hstay (α k) 1)) hm (h1.comp hα.tendsto_atTop)
  have hhalf : Tendsto (fun k => dist (γ (α k) 0) (γ (α k) 1)/r (α k)/2)
      atTop (𝓝 (dist a b/2)) := (h01.comp hα.tendsto_atTop).div_const 2
  refine ⟨c,hc,?_,?_,?_⟩
  · apply tendsto_nhds_unique h0m
    apply hhalf.congr
    intro k
    have hh := hg (α k) 0 quadraticMidpointTime
    change dist (γ (α k) 0) (m (α k))=|(0:ℝ)-1/2| *dist (γ (α k) 0) (γ (α k) 1) at hh
    simp only [Function.comp_apply]
    rw [hh]
    norm_num
    ring
  · apply tendsto_nhds_unique hm1
    apply hhalf.congr
    intro k
    have hh := hg (α k) quadraticMidpointTime 1
    change dist (m (α k)) (γ (α k) 1)=|(1/2:ℝ)-1| *dist (γ (α k) 0) (γ (α k) 1) at hh
    simp only [Function.comp_apply]
    rw [hh]
    norm_num
    ring
  · intro i
    apply pointed_fullMidpointDefect_zero (p∘α) ((z i)∘α) (r∘α) (ε∘α) (V∘α) (γ∘α)
      (fun k => hr (α k)) (hε.comp hα.tendsto_atTop) (fun k => hV (α k))
      (Eventually.of_forall (fun k => (hz i (α k)).trans (by
        change r (α k) ≤ 5*r (α k)
        nlinarith [hr (α k)])))
      (Eventually.of_forall (fun k t => hstay (α k) t))
      ((hVz i).comp hα.tendsto_atTop) (h0.comp hα.tendsto_atTop)
      (h1.comp hα.tendsto_atTop) hm ((hquad i).comp hα.tendsto_atTop)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
