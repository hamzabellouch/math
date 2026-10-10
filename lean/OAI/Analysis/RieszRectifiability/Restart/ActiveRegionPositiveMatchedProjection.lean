import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.CenteredPerturbedBallCoverage
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleFlatness

namespace OAI

/-!
# Matched projection at positive stopping scales

A local chart at a positive stopping scale supplies an approximating plane and
covers a disk in that plane by projecting the nearby limit surface. The same
plane controls the surface's normal deviation on the larger comparison ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_positive_matched_projection {n d : ℕ}
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
    (p : Ambient d) (hp : p ∈ Set.range f)
    (hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p)
    (hDsmall : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + 1))
    (r : ℝ) (hr : 0 < r)
    (hrsmall : 1024 * r ≤ cellRegionStoppingScale μ R hR k z Good p / 16) :
    ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
      (∀ x ∈ Set.range f ∩ closedBall p (1024 * r),
        infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤
          (67108864 * activeProjectionError d ε) * r) ∧
      closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
        P.orthogonalProjectionOnto '' (Set.range f ∩ closedBall p (r / 16)) := by
  let D := cellRegionStoppingScale μ R hR k z Good p
  let B := (17039360 * ε) / 63
  have hη : 0 ≤ activeProjectionError d ε := by unfold activeProjectionError; positivity
  have hweak : activeProjectionError d ε ≤ 1 / 128 := by linarith
  obtain ⟨q, hq, hqhi, hqlo, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good p hDpos hDsmall
  obtain ⟨hball, hscale⟩ := active_stopping_ball_chart_geometry μ R hR k z Good p q hqhi hqlo hnear
  obtain ⟨H, hLip, hSep, hError, hNormal, hDisp, hFinite, hCover⟩ :=
    exists_active_region_positive_scale_projection_chart μ R hR k z Good S hS
      ε hε hεtiny hweak hfit f hmodel q hq (closedBall p (D / 16)) hball hscale
  let P := (S q).direction
  have hpA : p ∈ Set.range f ∩ closedBall p (D / 16) :=
    ⟨hp, mem_closedBall_self (by dsimp [D]; positivity)⟩
  obtain ⟨a, ha⟩ := hCover hpA
  have hB : B ≤ 1 / 16 := by dsimp [B]; nlinarith
  have hamargin : dist a.val (P.orthogonalProjectionOnto q.center) ≤ (9 / 4 : ℝ) * q.radius := by
    have hda := hDisp a
    rw [ha] at hda
    rw [dist_comm] at hda
    have hpq := P.norm_starProjection_apply_le (p - q.center)
    rw [map_sub] at hpq
    have ht := dist_triangle a.val (P.orthogonalProjectionOnto p) (P.orthogonalProjectionOnto q.center)
    have hBm := mul_le_mul_of_nonneg_right hB q.radius_pos.le
    change dist a.val (P.orthogonalProjectionOnto p) ≤ (2 * B) * q.radius at hda
    change dist (P.orthogonalProjectionOnto p) (P.orthogonalProjectionOnto q.center) ≤
      dist p q.center at hpq
    nlinarith
  have hroom : dist a.val (P.orthogonalProjectionOnto q.center) + 2 * (r / 32) ≤
      (5 / 2 : ℝ) * q.radius := by
    change 64 * D < q.radius at hqlo
    change 1024 * r ≤ D / 16 at hrsmall
    linarith
  have hrad : latticeRadius R (k + (q.depth + 3)) = q.radius / 262144 := by
    rw [← Nat.add_assoc, latticeRadius_add]
    change q.radius * (1 / 64 : ℝ) ^ 3 = _
    norm_num
    ring
  have hK : ∀ x ∈ closedBall p (D / 2), D / 2 ≤ cellRegionStoppingScale μ R hR k z Good x := by
    intro x hx
    have h := cellRegionStoppingScale_le_add_dist μ R hR k z Good p x
    rw [dist_comm p x] at h
    have hxp : dist x p ≤ D / 2 := hx
    change D ≤ cellRegionStoppingScale μ R hR k z Good x + dist x p at h
    linarith
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) B (by dsimp [B]; positivity)
    hmodel.2.2.2.1 (closedBall p (D / 2)) (D / 2) hK (q.depth + 3) (by
      rw [hrad]
      have hBm := mul_le_mul_of_nonneg_right hB q.radius_pos.le
      change q.radius ≤ 4096 * D at hqhi
      change 0 < D at hDpos
      nlinarith)
  have hSurface : ∀ u, dist u a ≤ 2 * (r / 32) → H u ∈ Set.range f := by
    intro u hu
    have hd := hLip.dist_le_mul u a
    rw [ha] at hd
    norm_num at hd
    have hlocal : H u ∈ closedBall p (D / 2) := by
      change dist (H u) p ≤ D / 2
      change 1024 * r ≤ D / 16 at hrsmall
      linarith
    exact (hstable.symm ▸ (show H u ∈ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) ∩
      closedBall p (D / 2) from ⟨hFinite ⟨u, rfl⟩, hlocal⟩)).1
  have hKhalf : (Real.toNNReal (1008 * activeProjectionError d ε) : ℝ) ≤ 1 / 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    linarith
  have hLhalf : (Real.toNNReal (1012 * activeProjectionError d ε) : ℝ) ≤ 1 / 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    linarith
  have hProjected := centered_projection_disk_in_surface_ball P (P.orthogonalProjectionOnto q.center)
    ((5 / 2 : ℝ) * q.radius) H (Real.toNNReal (1008 * activeProjectionError d ε))
    (Real.toNNReal (1012 * activeProjectionError d ε)) hKhalf hLhalf hError hNormal
    a (r / 32) (by positivity) hroom (Set.range f) hSurface
  rw [ha, show 2 * (r / 32) = r / 16 by ring] at hProjected
  refine ⟨P, (hS q).2, ?_, hProjected⟩
  intro x hx
  have hxA : x ∈ Set.range f ∩ closedBall p (D / 16) :=
    ⟨hx.1, (closedBall_subset_closedBall hrsmall (x := p)) hx.2⟩
  have hcone := normal_projection_bound_on_chart_range P H
    (Real.toNNReal (1012 * activeProjectionError d ε)) 64 hNormal hSep
    x (hCover hxA) p ⟨a, ha⟩
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), NNReal.coe_ofNat] at hcone
  rw [infDist_affine_translate, submodule_infDist_eq_normal_projection]
  have hxp : dist x p ≤ 1024 * r := hx.2
  nlinarith [mul_le_mul_of_nonneg_left hxp hη, mul_nonneg hη hr.le]

end

end RieszRectifiability

end OAI
