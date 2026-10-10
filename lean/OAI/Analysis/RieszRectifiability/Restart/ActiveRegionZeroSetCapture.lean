import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionZeroSet
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitCapture

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem active_region_limit_captures_zero_set {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d) (hclosed : IsClosed (Set.range f))
    (htail : ∀ t (u : S (supportCellRoot μ R hR k z)),
      dist (activeRegionParameterMap μ R hR k z Good S hS t u) (f u) ≤
        ((17039360 * ε) / 63) * latticeRadius R (k + t)) :
    cellRegionZeroSet μ R hR k z Good ⊆ Set.range f := by
  intro x hx
  have hxzero : cellRegionStoppingScale μ R hR k z Good x = 0 := hx
  let C := 3 + 263168 * ε + (17039360 * ε) / 63
  have happrox : ∀ t, ∃ y ∈ Set.range f, dist x y ≤ C * latticeRadius R (k + t) := by
    intro t
    obtain ⟨q, hqA, hxq⟩ := exists_active_level_center_of_small_stopping_scale μ R hR k z Good t x
      (by rw [hxzero]; exact latticeRadius_pos R hR (k + t))
    have hq : q ∈ activeLevelIndex μ R hR k z Good t :=
      (mem_activeLevelIndex μ R hR k z Good t q).mpr hqA
    have hrad : q.radius = latticeRadius R (k + t) := by simp only [SupportCellDescendant.radius, hqA.1]
    have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit t
    obtain ⟨y, hy, hqy⟩ := active_cell_support_point_near_surface μ R hR k z q (S q) (hS q)
      ε (hfit q hqA.2) (activeRegionSurface μ R hR k z Good S hS t) (hcharts q hq)
      q.center q.center_mem_support (by rw [dist_self]; exact mul_nonneg (by norm_num) q.radius_pos.le)
    rw [activeRegionSurface_eq_image] at hy
    obtain ⟨a, ha, hay⟩ := hy
    let u : S (supportCellRoot μ R hR k z) := ⟨a, ha⟩
    have hyt : dist y (f u) ≤ ((17039360 * ε) / 63) * latticeRadius R (k + t) := by
      rw [← hay]
      exact htail t u
    have h1 := dist_triangle x q.center y
    have h2 := dist_triangle x y (f u)
    rw [hrad] at hqy
    refine ⟨f u, ⟨u, rfl⟩, ?_⟩
    dsimp [C]
    nlinarith
  have hdecay : Tendsto (fun t : ℕ => C * latticeRadius R (k + t)) atTop (𝓝 0) := by
    simp_rw [latticeRadius_add]
    simpa only [mul_zero] using!
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (by norm_num : (1 / 64 : ℝ) < 1)).const_mul (latticeRadius R k)).const_mul C
  have hcl : x ∈ closure (Set.range f) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨t, ht⟩ := (hdecay.eventually (gt_mem_nhds hδ)).exists
    obtain ⟨y, hy, hxy⟩ := happrox t
    exact ⟨y, hy, hxy.trans_lt ht⟩
  exact hclosed.closure_eq ▸ hcl

end

end RieszRectifiability

end OAI
