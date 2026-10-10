import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRequestedScaleSelection
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleFlatness
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitFlatness

namespace OAI

/-!
# Forward flatness at arbitrary scales

Parallel translates of fitting planes pass through the requested center while
their height errors remain controlled by the original plane distances. Active-cell
selection handles small radii, and the root plane handles large radii, both with
the same quantitative forward-flatness bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem infDist_parallel_plane_through_point_le {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (p x : Ambient d) :
    infDist x (AffineSubspace.mk' p S.direction : Set (Ambient d)) ≤
      infDist x (S : Set (Ambient d)) + infDist p (S : Set (Ambient d)) := by
  rw [infDist_affine_translate, submodule_infDist_eq_normal_projection]
  exact normal_projection_bound_by_plane_distances S x p

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hε hεtiny hsmall hfit hmodel

theorem active_region_limit_height_on_enlarged_active_ball
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (x : Ambient d) (hx : x ∈ Set.range f)
    (hlocal : x ∈ closedBall q.center ((17 / 8 : ℝ) * q.radius)) :
    infDist x (S q : Set (Ambient d)) ≤ (534000 * ε) * q.radius := by
  obtain ⟨u, rfl⟩ := hx
  let y := activeRegionParameterMap μ R hR k z Good S hS q.depth u
  have hy : y ∈ activeRegionSurface μ R hR k z Good S hS q.depth := by
    rw [activeRegionSurface_eq_image]
    exact ⟨u, u.property, rfl⟩
  have htail : dist y (f u) ≤ ((17039360 * ε) / 63) * q.radius := hmodel.2.2.2.1 q.depth u
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by nlinarith
  have hylocal : y ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
    have ht := dist_triangle y (f u) q.center
    have hxq : dist (f u) q.center ≤ (17 / 8 : ℝ) * q.radius := hlocal
    change dist y q.center ≤ (9 / 4 : ℝ) * q.radius
    nlinarith [mul_le_mul_of_nonneg_right hB q.radius_pos.le]
  have hqi : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  have hc := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth q hqi
  have hyplane := hc.height_on_inner_ball q (S q) ε _ y hy hylocal
  have hdist : infDist (f u) (S q : Set (Ambient d)) ≤
      infDist y (S q : Set (Ambient d)) + dist (f u) y := infDist_le_infDist_add_dist
  rw [dist_comm (f u) y] at hdist
  nlinarith [q.radius_pos]

theorem exists_active_region_low_stopping_scale_plane
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r)
    (hrtop : r ≤ latticeRadius R k / 2048)
    (hD : cellRegionStoppingScale μ R hR k z Good p ≤ 16 * r) :
    ∃ W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n W ∧ p ∈ W ∧
      ∀ x ∈ Set.range f ∩ closedBall p r,
        infDist x (W : Set (Ambient d)) ≤ (140000000000 * ε) * r := by
  obtain ⟨t, q, hqF, hqlo, hqhi, hnear⟩ := exists_active_cell_at_requested_radius
    μ R hR k z Good p (128 * r) (by positivity) (by linarith) (by linarith)
  have hq := ((mem_activeLevelIndex μ R hR k z Good t q).mp hqF).2
  let : Nonempty (S q) := (hS q).1.to_subtype
  let W := AffineSubspace.mk' p (S q).direction
  have hW : IsAffineNPlane n W := by
    refine ⟨AffineSubspace.mk'_nonempty _ _, ?_⟩
    rw [AffineSubspace.direction_mk']
    exact (hS q).2
  have hpW : p ∈ W := by apply AffineSubspace.mem_mk'.mpr; simpa only [vsub_self] using! (S q).direction.zero_mem
  have hpq : p ∈ closedBall q.center ((17 / 8 : ℝ) * q.radius) := by
    change dist p q.center ≤ (17 / 8 : ℝ) * q.radius
    nlinarith [q.radius_pos]
  have hpheight := active_region_limit_height_on_enlarged_active_ball μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel q hq p hp hpq
  refine ⟨W, hW, hpW, ?_⟩
  intro x hx
  have hxq : x ∈ closedBall q.center ((17 / 8 : ℝ) * q.radius) := by
    have ht := dist_triangle x p q.center
    have hxp : dist x p ≤ r := hx.2
    change dist x q.center ≤ (17 / 8 : ℝ) * q.radius
    nlinarith
  have hxheight := active_region_limit_height_on_enlarged_active_ball μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel q hq x hx.1 hxq
  have hparallel := infDist_parallel_plane_through_point_le (S q) p x
  change infDist x (W : Set (Ambient d)) ≤ _ at hparallel
  nlinarith [mul_le_mul_of_nonneg_left hqhi hε.le, mul_pos hε hr]

omit hεtiny hsmall hfit in
theorem exists_active_region_large_radius_plane
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r)
    (hrlarge : latticeRadius R k / 2048 ≤ r) :
    ∃ W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n W ∧ p ∈ W ∧
      ∀ x ∈ Set.range f ∩ closedBall p r,
        infDist x (W : Set (Ambient d)) ≤ (140000000000 * ε) * r := by
  let root := supportCellRoot μ R hR k z
  let : Nonempty (S root) := (hS root).1.to_subtype
  let W := AffineSubspace.mk' p (S root).direction
  have hW : IsAffineNPlane n W := by
    refine ⟨AffineSubspace.mk'_nonempty _ _, ?_⟩
    rw [AffineSubspace.direction_mk']
    exact (hS root).2
  have hpW : p ∈ W := by apply AffineSubspace.mem_mk'.mpr; simpa only [vsub_self] using! (S root).direction.zero_mem
  have hheight (x : Ambient d) (hx : x ∈ Set.range f) :
      infDist x (S root : Set (Ambient d)) ≤ ((17039360 * ε) / 63) * latticeRadius R k := by
    obtain ⟨u, rfl⟩ := hx
    have h := hmodel.2.2.2.1 0 u
    simp only [activeRegionParameterMap, id_eq, Nat.add_zero] at h
    exact (infDist_le_dist_of_mem u.property).trans (by rwa [dist_comm])
  refine ⟨W, hW, hpW, ?_⟩
  intro x hx
  have hparallel := infDist_parallel_plane_through_point_le (S root) p x
  change infDist x (W : Set (Ambient d)) ≤ _ at hparallel
  have hscale := mul_le_mul_of_nonneg_left hrlarge hε.le
  nlinarith [hheight x hx.1, hheight p hp, mul_pos hε hr]

theorem exists_active_region_high_stopping_scale_plane
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r)
    (hrsmall : r ≤ latticeRadius R k / 2048)
    (hD : latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good p) :
    ∃ W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n W ∧ p ∈ W ∧
      ∀ x ∈ Set.range f ∩ closedBall p r,
        infDist x (W : Set (Ambient d)) ≤ (3456 * activeProjectionError d ε) * r := by
  let root := supportCellRoot μ R hR k z
  let P := (S root).direction
  let W := AffineSubspace.mk' p P
  let T := activeRegionTransitionMap μ R hR k z Good S hS 0 2
  let B := (17039360 * ε) / 63
  have hr0 := latticeRadius_pos R hR k
  have hB : B ≤ 1 / 16 := by dsimp [B]; nlinarith
  have hη : 0 ≤ activeProjectionError d ε := by unfold activeProjectionError; positivity
  have hK : ∀ x ∈ closedBall p r,
      latticeRadius R (k + 1) / 2 ≤ cellRegionStoppingScale μ R hR k z Good x := by
    intro x hx
    have ht := cellRegionStoppingScale_le_add_dist μ R hR k z Good p x
    rw [dist_comm p x] at ht
    have hxp : dist x p ≤ r := hx
    rw [latticeRadius_succ] at hD ⊢
    linarith
  have hr2 : latticeRadius R (k + 2) = latticeRadius R k / 4096 := by
    rw [latticeRadius_add]; norm_num; ring
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) B (by dsimp [B]; positivity)
    hmodel.2.2.2.1 (closedBall p r) (latticeRadius R (k + 1) / 2) hK 2 (by
      rw [hr2, latticeRadius_succ]
      nlinarith [mul_le_mul_of_nonneg_right hB hr0.le])
  have hpfinite : p ∈ activeRegionSurface μ R hR k z Good S hS (0 + 2) :=
    (hstable ▸ (show p ∈ Set.range f ∩ closedBall p r from ⟨hp, mem_closedBall_self hr.le⟩)).1
  rw [activeRegionSurface_add] at hpfinite
  obtain ⟨v, hv, hvp⟩ := hpfinite
  change T v = p at hvp
  have hW : IsAffineNPlane n W := by
    refine ⟨AffineSubspace.mk'_nonempty _ _, ?_⟩
    rw [AffineSubspace.direction_mk']
    exact (hS root).2
  have hpW : p ∈ W := by apply AffineSubspace.mem_mk'.mpr; simpa only [vsub_self] using! P.zero_mem
  refine ⟨W, hW, hpW, ?_⟩
  intro x hx
  have hxfinite : x ∈ activeRegionSurface μ R hR k z Good S hS (0 + 2) := (hstable ▸ hx).1
  rw [activeRegionSurface_add] at hxfinite
  obtain ⟨u, hu, hux⟩ := hxfinite
  change T u = x at hux
  have hres := activeRegionTransitionMap_surface_residual_le μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit 0 2 u v hu hv
  have hdist := (activeRegionTransitionMap_surface_dist_bounds μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit 0 2 u v hu hv).1
  norm_num at hres hdist
  change ‖(T u - T v) - (u - v)‖ ≤ _ at hres
  change (1 / 16 : ℝ) * dist u v ≤ dist (T u) (T v) at hdist
  have hdir : u - v ∈ P := AffineSubspace.vsub_mem_direction hu hv
  have hz : (Pᗮ : Submodule ℝ (Ambient d)).starProjection (u - v) = 0 := by
    have h := P.starProjection_add_starProjection_orthogonal (u - v)
    rw [P.starProjection_eq_self_iff.mpr hdir, add_eq_left] at h
    exact h
  have hproj := (Pᗮ : Submodule ℝ (Ambient d)).norm_starProjection_apply_le
    ((T u - T v) - (u - v))
  rw [map_sub, hz, sub_zero] at hproj
  have hnormal := hproj.trans hres
  rw [hux, hvp] at hnormal hdist
  rw [infDist_affine_translate p x P, submodule_infDist_eq_normal_projection]
  have hscale : dist u v ≤ 16 * r := by have hxp : dist x p ≤ r := hx.2; linarith
  nlinarith [mul_le_mul_of_nonneg_left hscale hη]

theorem exists_active_region_all_scale_forward_plane
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r) :
    ∃ W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n W ∧ p ∈ W ∧
      ∀ x ∈ Set.range f ∩ closedBall p r,
        infDist x (W : Set (Ambient d)) ≤
          (140000000000 * (ε + activeProjectionError d ε)) * r := by
  have hη : 0 ≤ activeProjectionError d ε := by unfold activeProjectionError; positivity
  by_cases hlarge : latticeRadius R k / 2048 ≤ r
  · obtain ⟨W, hW, hpW, hheight⟩ := exists_active_region_large_radius_plane μ R hR k z Good S hS
      ε hε f hmodel p hp r hr hlarge
    refine ⟨W, hW, hpW, ?_⟩
    intro x hx
    exact (hheight x hx).trans (mul_le_mul_of_nonneg_right (by nlinarith) hr.le)
  have hrsmall := (not_le.mp hlarge).le
  by_cases hhigh : latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good p
  · obtain ⟨W, hW, hpW, hheight⟩ := exists_active_region_high_stopping_scale_plane μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel p hp r hr hrsmall hhigh
    refine ⟨W, hW, hpW, ?_⟩
    intro x hx
    exact (hheight x hx).trans (mul_le_mul_of_nonneg_right (by nlinarith) hr.le)
  by_cases hnear : r ≤ cellRegionStoppingScale μ R hR k z Good p / 16
  · have hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p := by linarith
    obtain ⟨W, hW, hpW, hheight⟩ := exists_active_region_positive_scale_centered_plane μ R hR k z
      Good S hS ε hε hεtiny hsmall hfit f hmodel p hp hDpos (not_le.mp hhigh)
    refine ⟨W, hW, hpW, ?_⟩
    intro x hx
    exact (hheight r hr hnear x hx).trans (mul_le_mul_of_nonneg_right (by nlinarith) hr.le)
  obtain ⟨W, hW, hpW, hheight⟩ := exists_active_region_low_stopping_scale_plane μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel p hp r hr hrsmall (by linarith [not_le.mp hnear])
  refine ⟨W, hW, hpW, ?_⟩
  intro x hx
  exact (hheight x hx).trans (mul_le_mul_of_nonneg_right (by nlinarith) hr.le)

end

end RieszRectifiability

end OAI
