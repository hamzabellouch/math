import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLargeScaleCharts
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionTransitionDistortion
import OAI.Analysis.RieszRectifiability.Surfaces.PlaneChartBallArea

namespace OAI

/-!
# Local charts at high stopping scales

Two active projection steps transport a root-plane disk to a bilipschitz chart
covering the high-stopping-scale part of the limit model in a given ball.
The distance bounds on this chart yield local Hausdorff measure estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

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

theorem exists_active_region_high_scale_local_bilipschitz_chart
    (p : Ambient d) (r : ℝ) (hr : 0 < r) (A : Set (Ambient d)) (hA : A ⊆ closedBall p r)
    (hD : ∀ x ∈ A, latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ H : closedBall
        ((S (supportCellRoot μ R hR k z)).direction.orthogonalProjectionOnto p) ρ → Ambient d,
      LipschitzWith 4 H ∧ AntilipschitzWith 16 H ∧ Set.range f ∩ A ⊆ Set.range H := by
  let P := (S (supportCellRoot μ R hR k z)).direction
  let B := (17039360 * ε) / 63
  let ρ := r + 2 * B * latticeRadius R k
  have hρ : 0 < ρ := by dsimp [ρ, B]; have hr0 := latticeRadius_pos R hR k; positivity
  obtain ⟨g, hgLip, _, hcoords, hgRange⟩ := exists_affine_plane_disk_chart
    (S (supportCellRoot μ R hR k z)) (hS _).1 (P.orthogonalProjectionOnto p) ρ
  let T := activeRegionTransitionMap μ R hR k z Good S hS 0 2
  have hdist (u v) : (1 / 16 : ℝ) * dist (g u) (g v) ≤ dist (T (g u)) (T (g v)) ∧
      dist (T (g u)) (T (g v)) ≤ 4 * dist (g u) (g v) := by
    have h := activeRegionTransitionMap_surface_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit 0 2 (g u) (g v) (hcoords u).1 (hcoords v).1
    norm_num at h
    exact h
  have hLip : LipschitzWith 4 (T ∘ g) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hb := hgLip.dist_le_mul u v
    norm_num at hb ⊢
    change dist (T (g u)) (T (g v)) ≤ 4 * dist u v
    linarith [(hdist u v).2]
  have hsep : AntilipschitzWith 16 (T ∘ g) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    have hp : dist u v ≤ dist (g u) (g v) := by
      change dist u.val v.val ≤ dist (g u) (g v)
      rw [← (hcoords u).2, ← (hcoords v).2]
      have h := P.norm_starProjection_apply_le (g u - g v)
      rw [map_sub] at h
      exact h
    norm_num
    change dist u v ≤ 16 * dist (T (g u)) (T (g v))
    linarith [(hdist u v).1]
  have hr0 := latticeRadius_pos R hR k
  have hB : B ≤ 1 / 16 := by dsimp [B]; linarith
  have hBm := mul_le_mul_of_nonneg_right hB hr0.le
  have hr2 : latticeRadius R (k + 2) = latticeRadius R k / 4096 := by
    rw [latticeRadius_add]
    norm_num
    ring
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) B (by dsimp [B]; positivity)
    hmodel.2.2.2.1 A (latticeRadius R (k + 1)) hD 2 (by
      rw [hr2, latticeRadius_succ]
      nlinarith)
  refine ⟨ρ, hρ, T ∘ g, hLip, hsep, ?_⟩
  intro x hx
  have hx2 : x ∈ activeRegionSurface μ R hR k z Good S hS (0 + 2) := (hstable ▸ hx).1
  rw [activeRegionSurface_add] at hx2
  obtain ⟨y, hy, hTy⟩ := hx2
  change T y = x at hTy
  have hmove := active_region_transition_surface_movement μ R hR k z Good S hS ε hε.le f hmodel 0 2 y hy
  change dist (T y) y ≤ (2 * B) * latticeRadius R k at hmove
  rw [hTy] at hmove
  have hyp : dist y p ≤ ρ := by
    have ht := dist_triangle y x p
    rw [dist_comm y x] at ht
    have hxp : dist x p ≤ r := hA hx.2
    dsimp [ρ]
    linarith
  have hproject := P.norm_starProjection_apply_le (y - p)
  rw [map_sub, ← dist_eq_norm (P.starProjection y) (P.starProjection p), ← dist_eq_norm y p] at hproject
  have hyg : y ∈ Set.range g := by
    rw [hgRange]
    exact ⟨hy, hproject.trans hyp⟩
  obtain ⟨u, hu⟩ := hyg
  exact ⟨u, by change T (g u) = x; rw [hu]; exact hTy⟩

theorem active_region_high_scale_local_ball_area_le
    (p : Ambient d) (r : ℝ) (hr : 0 < r) (A : Set (Ambient d)) (hA : A ⊆ closedBall p r)
    (hD : ∀ x ∈ A, latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good x) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ A) ≤
      planeChartBallAreaConstant n 4 16 * (ENNReal.ofReal r) ^ n := by
  obtain ⟨ρ, _, H, hLip, hsep, hcover⟩ :=
    exists_active_region_high_scale_local_bilipschitz_chart μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel p r hr A hA hD
  have hsub : Set.range f ∩ A ⊆ Set.range H ∩ closedBall p r :=
    fun _ hx => ⟨hcover hx, hA hx.2⟩
  exact (measure_mono hsub).trans
    (plane_chart_ball_hausdorffMeasure_le (S (supportCellRoot μ R hR k z)).direction
      (hS _).2 _ H 4 16 (by norm_num) hLip hsep p r hr)

end

end RieszRectifiability

end OAI
