import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionHighScaleLocalArea

namespace OAI

/-!
# Inner disks at high stopping scales

A point of the limit model at high stopping scale admits a centered disk chart
obtained by transporting a root-plane disk through two active projection steps.
Quantitative distance bounds control the image inside the prescribed ambient ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_high_scale_inner_disk {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f)
    (hD : latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good p)
    (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ latticeRadius R k / 128) :
    ∃ a : (S (supportCellRoot μ R hR k z)).direction,
      ∃ H : closedBall a (r / 4) → Ambient d,
        LipschitzWith 4 H ∧ AntilipschitzWith 16 H ∧
        H ⟨a, mem_closedBall_self (by positivity)⟩ = p ∧
        Set.range H ⊆ Set.range f ∩ closedBall p r := by
  let P := (S (supportCellRoot μ R hR k z)).direction
  let B := (17039360 * ε) / 63
  have hr0 := latticeRadius_pos R hR k
  have hB : B ≤ 1 / 16 := by dsimp [B]; linarith
  have hBm := mul_le_mul_of_nonneg_right hB hr0.le
  have hrad : latticeRadius R (k + 2) = latticeRadius R k / 4096 := by
    rw [latticeRadius_add]
    norm_num
    ring
  rw [latticeRadius_succ] at hD
  have hK : ∀ x ∈ closedBall p (latticeRadius R k / 128),
      latticeRadius R k / 128 ≤ cellRegionStoppingScale μ R hR k z Good x := by
    intro x hx
    have h := cellRegionStoppingScale_le_add_dist μ R hR k z Good p x
    rw [dist_comm p x] at h
    have hb : dist x p ≤ latticeRadius R k / 128 := hx
    linarith
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) B (by dsimp [B]; positivity)
    hmodel.2.2.2.1 (closedBall p (latticeRadius R k / 128))
    (latticeRadius R k / 128) hK 2 (by rw [hrad]; nlinarith)
  have hpfinite : p ∈ activeRegionSurface μ R hR k z Good S hS (0 + 2) :=
    (hstable ▸ (show p ∈ Set.range f ∩ closedBall p (latticeRadius R k / 128) from
      ⟨hp, mem_closedBall_self (by positivity)⟩)).1
  rw [activeRegionSurface_add] at hpfinite
  obtain ⟨y, hy, hTy⟩ := hpfinite
  change y ∈ S (supportCellRoot μ R hR k z) at hy
  let T := activeRegionTransitionMap μ R hR k z Good S hS 0 2
  change T y = p at hTy
  obtain ⟨g, hgLip, _, hcoords, hgrange⟩ := exists_affine_plane_disk_chart
    (S (supportCellRoot μ R hR k z)) (hS _).1 (P.orthogonalProjectionOnto y) (r / 4)
  let a0 : closedBall (P.orthogonalProjectionOnto y) (r / 4) :=
    ⟨P.orthogonalProjectionOnto y, mem_closedBall_self (by positivity)⟩
  have hyg : y ∈ Set.range g := by
    rw [hgrange]
    refine ⟨hy, ?_⟩
    change P.orthogonalProjectionOnto y ∈ closedBall (P.orthogonalProjectionOnto y) (r / 4)
    exact mem_closedBall_self (by linarith)
  obtain ⟨v, hv⟩ := hyg
  have hva : v = a0 := by
    apply Subtype.ext
    rw [← (hcoords v).2, hv]
  have hga : g a0 = y := by rw [← hva]; exact hv
  let H := T ∘ g
  have hdist (u v) : (1 / 16 : ℝ) * dist (g u) (g v) ≤ dist (H u) (H v) ∧
      dist (H u) (H v) ≤ 4 * dist (g u) (g v) := by
    have h := activeRegionTransitionMap_surface_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit 0 2 (g u) (g v) (hcoords u).1 (hcoords v).1
    norm_num at h
    exact h
  have hLip : LipschitzWith 4 H := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hb := hgLip.dist_le_mul u v
    norm_num at hb ⊢
    linarith [(hdist u v).2]
  have hsep : AntilipschitzWith 16 H := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    have hproj : dist u v ≤ dist (g u) (g v) := by
      change dist u.val v.val ≤ dist (g u) (g v)
      rw [← (hcoords u).2, ← (hcoords v).2]
      have h := P.norm_starProjection_apply_le (g u - g v)
      rw [map_sub] at h
      exact h
    norm_num
    linarith [(hdist u v).1]
  have hcenter : H a0 = p := by
    change T (g a0) = p
    rw [hga, hTy]
  refine ⟨P.orthogonalProjectionOnto y, H, hLip, hsep, hcenter, ?_⟩
  rintro _ ⟨u, rfl⟩
  have hball : H u ∈ closedBall p r := by
    have h := hLip.dist_le_mul u a0
    rw [hcenter] at h
    have hu : dist u a0 ≤ r / 4 := u.property
    norm_num at h
    change dist (H u) p ≤ r
    linarith
  have hballK : H u ∈ closedBall p (latticeRadius R k / 128) :=
    le_trans hball hrsmall
  have hfinite : H u ∈ activeRegionSurface μ R hR k z Good S hS (0 + 2) := by
    rw [activeRegionSurface_add]
    exact ⟨g u, (hcoords u).1, rfl⟩
  exact ⟨(hstable.symm ▸ (show H u ∈ activeRegionSurface μ R hR k z Good S hS 2 ∩
    closedBall p (latticeRadius R k / 128) from ⟨hfinite, hballK⟩)).1, hball⟩

end

end RieszRectifiability

end OAI
