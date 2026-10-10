import OAI.Geometry.RCD.Metric.PointedLiftDistances
import OAI.Geometry.RCD.Transport.RadialGeodesic

namespace OAI

/-! # Short metric-limit segments are obtained from original geodesics -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [ProperSpace Y]

theorem pointed_metric_limit_segment (hgeo : IsGeodesicSpace X)
    {q y z : Y} (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0<r k) (hε0 : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k))
    (hy : dist y q<1/128) (hz : dist z q<1/128) (t : Time) :
    ∃ b : Y, dist b q≤1/32 ∧ dist y b=(t:ℝ)*dist y z ∧
      dist b z=(1-(t:ℝ))*dist y z := by
  obtain ⟨x,hx,hVx⟩ := pointed_metric_interior_lift p r ε V hr hε0 hV
    (by norm_num : (1/128:ℝ)<5) hy
  obtain ⟨x',hx',hVx'⟩ := pointed_metric_interior_lift p r ε V hr hε0 hV
    (by norm_num : (1/128:ℝ)<5) hz
  choose γ h0 h1 hγ using fun k => hgeo (x k) (x' k)
  let m k := γ k t
  have hdist0 (k : ℕ) : dist (x k) (m k)=(t:ℝ)*dist (x k) (x' k) := by
    have hh := hγ k 0 t
    rw [h0 k,h1 k] at hh
    change dist (x k) (γ k t)=|(0:ℝ)-(t:ℝ)| * dist (x k) (x' k) at hh
    simpa only [m,zero_sub,abs_neg,abs_of_nonneg t.2.1] using hh
  have hdist1 (k : ℕ) : dist (m k) (x' k)=(1-(t:ℝ))*dist (x k) (x' k) := by
    have hh := hγ k t 1
    rw [h0 k,h1 k] at hh
    change dist (γ k t) (x' k)=|(t:ℝ)-1| * dist (x k) (x' k) at hh
    simpa only [m,abs_of_nonpos (sub_nonpos.mpr t.2.2),neg_sub] using hh
  let P k := dist (x k) (p k)≤(1/128:ℝ)*r k ∧
    dist (x' k) (p k)≤(1/128:ℝ)*r k ∧ ε k≤1/256
  have hP : ∀ᶠ k in atTop, P k := by
    filter_upwards [hx,hx',hε0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/256))]
      with k hk hk' he
    exact ⟨hk,hk',he.le⟩
  have hm (k : ℕ) (hk : P k) : dist (m k) (p k)≤(3/128:ℝ)*r k := by
    have hxy := dist_triangle (x k) (p k) (x' k)
    rw [dist_comm (p k) (x' k)] at hxy
    have ht : dist (x k) (m k)≤dist (x k) (x' k) := by
      rw [hdist0]
      exact mul_le_of_le_one_left dist_nonneg t.2.2
    have hb := dist_triangle (m k) (x k) (p k)
    rw [dist_comm (m k) (x k)] at hb
    linarith [hk.1,hk.2.1]
  have hxmS : ∀ᶠ k in atTop, dist (m k) (p k)≤5*r k := by
    filter_upwards [hP] with k hk
    exact (hm k hk).trans (by nlinarith [hr k])
  have hxS : ∀ᶠ k in atTop, dist (x k) (p k)≤5*r k := by
    filter_upwards [hx] with k hk
    exact hk.trans (by nlinarith [hr k])
  have hx'S : ∀ᶠ k in atTop, dist (x' k) (p k)≤5*r k := by
    filter_upwards [hx'] with k hk
    exact hk.trans (by nlinarith [hr k])
  have hmb (k : ℕ) (hk : P k) : dist (V k (m k)) q≤1/32 := by
    have hp : dist (p k) (p k)≤5*r k := by
      simp only [dist_self]
      exact mul_nonneg (by norm_num) (hr k).le
    have hd := (abs_le.mp ((hV k).2.1 (m k) (p k)
      ((hm k hk).trans (by nlinarith [hr k])) hp)).2
    have ht := dist_triangle (V k (m k)) (V k (p k)) q
    have hratio : dist (m k) (p k)/r k≤3/128 := (div_le_iff₀ (hr k)).mpr (hm k hk)
    linarith [(hV k).1,hk.2.2]
  let z' k := if P k then V k (m k) else q
  have hz' (k : ℕ) : z' k∈closedBall q (1/32) := by
    dsimp [z']
    split_ifs with hk
    · exact hmb k hk
    · simp
  obtain ⟨b,hb,α,hα,hlim⟩ := (isCompact_closedBall q (1/32:ℝ)).tendsto_subseq hz'
  have hm0 : Tendsto (fun k => V (α k) (m (α k))) atTop (𝓝 b) := by
    apply hlim.congr'
    filter_upwards [hα.tendsto_atTop.eventually hP] with k hk
    exact ite_eq_left hk
  have hxy := pointed_lift_distance_tendsto p r ε V hε0 hV x x' hxS hx'S hVx hVx'
  have hxb := pointed_lift_distance_tendsto (p∘α) (r∘α) (ε∘α) (V∘α)
    (hε0.comp hα.tendsto_atTop) (fun k => hV (α k)) (x∘α) (m∘α)
    (hα.tendsto_atTop.eventually hxS) (hα.tendsto_atTop.eventually hxmS)
    (hVx.comp hα.tendsto_atTop) hm0
  have hby := pointed_lift_distance_tendsto (p∘α) (r∘α) (ε∘α) (V∘α)
    (hε0.comp hα.tendsto_atTop) (fun k => hV (α k)) (m∘α) (x'∘α)
    (hα.tendsto_atTop.eventually hxmS) (hα.tendsto_atTop.eventually hx'S)
    hm0 (hVx'.comp hα.tendsto_atTop)
  refine ⟨b,hb,?_,?_⟩
  · apply tendsto_nhds_unique hxb
    convert (hxy.comp hα.tendsto_atTop).const_mul (t:ℝ) using 1
    funext k
    simp only [Function.comp_apply,hdist0]
    ring
  · apply tendsto_nhds_unique hby
    convert (hxy.comp hα.tendsto_atTop).const_mul (1-(t:ℝ)) using 1
    funext k
    simp only [Function.comp_apply,hdist1]
    ring

end RegularPointCoordinates

end

end OAI
