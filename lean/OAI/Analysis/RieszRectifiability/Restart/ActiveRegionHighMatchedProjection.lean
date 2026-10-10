import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.CenteredPerturbedBallCoverage
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionAllScaleForwardFlatness
import OAI.Analysis.RieszRectifiability.Projections.ChartProjectionResidual

namespace OAI

/-!
# Matched projections above the first stopping scale

When the stopping scale is at least the first descendant scale, the root plane
provides both a quantitative forward flatness bound and a projected disk in a
small ball of the limit surface. The argument uses finite-stage stabilization
and residual estimates for a transported affine-plane chart.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_high_matched_projection {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 4096)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r)
    (hrsmall : r ≤ latticeRadius R k / 2097152)
    (hD : latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good p) :
    ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
      (∀ x ∈ Set.range f ∩ closedBall p (1024 * r),
        infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤
          (4194304 * activeProjectionError d ε) * r) ∧
      closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
        P.orthogonalProjectionOnto '' (Set.range f ∩ closedBall p (r / 16)) := by
  let root := supportCellRoot μ R hR k z
  let P := (S root).direction
  let B := (17039360 * ε) / 63
  let ρ := 1025 * r + (2 * B) * latticeRadius R k
  let T := activeRegionTransitionMap μ R hR k z Good S hS 0 2
  have hr0 := latticeRadius_pos R hR k
  have hη : 0 ≤ activeProjectionError d ε := by unfold activeProjectionError; positivity
  have hweak : activeProjectionError d ε ≤ 1 / 128 := by linarith
  have hB : B ≤ 1 / 16 := by dsimp [B]; nlinarith
  have hK : ∀ x ∈ closedBall p (1024 * r),
      latticeRadius R (k + 1) / 2 ≤ cellRegionStoppingScale μ R hR k z Good x := by
    intro x hx
    have ht := cellRegionStoppingScale_le_add_dist μ R hR k z Good p x
    rw [dist_comm p x] at ht
    have hxp : dist x p ≤ 1024 * r := hx
    rw [latticeRadius_succ] at hD ⊢
    linarith
  have hr2 : latticeRadius R (k + 2) = latticeRadius R k / 4096 := by
    rw [latticeRadius_add]; norm_num; ring
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) B (by dsimp [B]; positivity)
    hmodel.2.2.2.1 (closedBall p (1024 * r)) (latticeRadius R (k + 1) / 2) hK 2 (by
      rw [hr2, latticeRadius_succ]
      nlinarith [mul_le_mul_of_nonneg_right hB hr0.le])
  obtain ⟨g, hgLip, hgNormal, hcoords, hgRange⟩ := exists_affine_plane_disk_chart
    (S root) (hS root).1 (P.orthogonalProjectionOnto p) ρ
  let H := T ∘ g
  have hdist (u v) : (1 / 16 : ℝ) * dist (g u) (g v) ≤ dist (H u) (H v) ∧
      dist (H u) (H v) ≤ 4 * dist (g u) (g v) := by
    have h := activeRegionTransitionMap_surface_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hweak hfit 0 2 (g u) (g v) (hcoords u).1 (hcoords v).1
    norm_num at h
    exact h
  have hLip : LipschitzWith 4 H := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hbase := hgLip.dist_le_mul u v
    norm_num at hbase ⊢
    nlinarith [(hdist u v).2]
  have hSep : AntilipschitzWith 16 H := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    have hproj : dist u v ≤ dist (g u) (g v) := by
      change dist u.val v.val ≤ dist (g u) (g v)
      rw [← (hcoords u).2, ← (hcoords v).2]
      have h := P.norm_starProjection_apply_le (g u - g v)
      rw [map_sub] at h
      exact h
    norm_num
    nlinarith [(hdist u v).1]
  have hres (u v) : ‖(T (g u) - T (g v)) - (g u - g v)‖ ≤
      (216 * activeProjectionError d ε) * dist u v := by
    have h := activeRegionTransitionMap_surface_residual_le μ R hR k z Good S hS
      ε hε hεtiny hweak hfit 0 2 (g u) (g v) (hcoords u).1 (hcoords v).1
    have hb := hgLip.dist_le_mul u v
    norm_num at h hb
    change ‖(T (g u) - T (g v)) - (g u - g v)‖ ≤ _ at h
    nlinarith [mul_le_mul_of_nonneg_left hb hη]
  have hError := projected_chart_error_lipschitz_of_residual P _ g T
    (216 * activeProjectionError d ε) (by positivity) (fun u => (hcoords u).2) hres
  have hNormal : LipschitzWith (Real.toNNReal (216 * activeProjectionError d ε))
      (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (H u)) := by
    simpa only [NNReal.coe_zero, add_zero] using! normal_chart_lipschitz_of_residual P _ g T
      (216 * activeProjectionError d ε) (by positivity) 0 hgNormal hres
  have hFinite : Set.range H ⊆ activeRegionSurface μ R hR k z Good S hS (0 + 2) := by
    rintro _ ⟨u, rfl⟩
    rw [activeRegionSurface_add]
    exact ⟨g u, (hcoords u).1, rfl⟩
  have hCover : Set.range f ∩ closedBall p (1024 * r) ⊆ Set.range H := by
    intro x hx
    have hx2 : x ∈ activeRegionSurface μ R hR k z Good S hS (0 + 2) := (hstable ▸ hx).1
    rw [activeRegionSurface_add] at hx2
    obtain ⟨y, hy, hTy⟩ := hx2
    change T y = x at hTy
    have hmove := active_region_transition_surface_movement μ R hR k z Good S hS ε hε.le
      f hmodel 0 2 y hy
    change dist (T y) y ≤ (2 * B) * latticeRadius R k at hmove
    rw [hTy] at hmove
    have hyp : dist y p ≤ ρ := by
      have ht := dist_triangle y x p
      rw [dist_comm y x] at ht
      have hxp : dist x p ≤ 1024 * r := hx.2
      dsimp [ρ]
      linarith
    have hpj := P.norm_starProjection_apply_le (y - p)
    rw [map_sub] at hpj
    have hyg : y ∈ Set.range g := by rw [hgRange]; exact ⟨hy, hpj.trans hyp⟩
    obtain ⟨u, hu⟩ := hyg
    exact ⟨u, by change T (g u) = x; rw [hu]; exact hTy⟩
  obtain ⟨a, ha⟩ := hCover ⟨hp, mem_closedBall_self (by positivity)⟩
  have hroom : dist a.val (P.orthogonalProjectionOnto p) + 2 * (r / 32) ≤ ρ := by
    have hmove := active_region_transition_surface_movement μ R hR k z Good S hS ε hε.le
      f hmodel 0 2 (g a) (hcoords a).1
    change dist (H a) (g a) ≤ (2 * B) * latticeRadius R k at hmove
    rw [ha] at hmove
    have hpj := P.norm_starProjection_apply_le (g a - p)
    rw [map_sub] at hpj
    change dist (P.orthogonalProjectionOnto (g a)) (P.orthogonalProjectionOnto p) ≤ dist (g a) p at hpj
    rw [(hcoords a).2, dist_comm (g a) p] at hpj
    dsimp [ρ]
    linarith
  have hSurface : ∀ u, dist u a ≤ 2 * (r / 32) → H u ∈ Set.range f := by
    intro u hu
    have hd := hLip.dist_le_mul u a
    rw [ha] at hd
    norm_num at hd
    have hlocal : H u ∈ closedBall p (1024 * r) := by
      change dist (H u) p ≤ 1024 * r
      linarith
    exact (hstable.symm ▸ (show H u ∈ activeRegionSurface μ R hR k z Good S hS 2 ∩
      closedBall p (1024 * r) from ⟨hFinite ⟨u, rfl⟩, hlocal⟩)).1
  have hHalf : (Real.toNNReal (216 * activeProjectionError d ε) : ℝ) ≤ 1 / 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    linarith
  have hProjected := centered_projection_disk_in_surface_ball P (P.orthogonalProjectionOnto p) ρ H
    (Real.toNNReal (216 * activeProjectionError d ε)) (Real.toNNReal (216 * activeProjectionError d ε))
    hHalf hHalf hError hNormal a (r / 32) (by positivity) hroom (Set.range f) hSurface
  rw [ha, show 2 * (r / 32) = r / 16 by ring] at hProjected
  refine ⟨P, (hS root).2, ?_, hProjected⟩
  intro x hx
  have hcone := normal_projection_bound_on_chart_range P H
    (Real.toNNReal (216 * activeProjectionError d ε)) 16 hNormal hSep x (hCover hx) p ⟨a, ha⟩
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), NNReal.coe_ofNat] at hcone
  rw [infDist_affine_translate, submodule_infDist_eq_normal_projection]
  have hxp : dist x p ≤ 1024 * r := hx.2
  nlinarith [mul_le_mul_of_nonneg_left hxp hη, mul_nonneg hη hr.le]

end

end RieszRectifiability

end OAI
