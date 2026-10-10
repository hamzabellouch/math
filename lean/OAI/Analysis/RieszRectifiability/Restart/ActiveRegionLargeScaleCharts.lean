import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionTransitionMovement

namespace OAI

/-!
# Large-scale charts for active-region limits

The portion of an active-region limit model with large stopping scale is covered by
a root-plane disk chart transported through two active projection steps. The resulting
chart has Lipschitz bound equal to the square of the global projection bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_large_scale_chart {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 ≤ ε)
    (hεtiny : ε ≤ 1 / 268435456)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (A : Set (Ambient d)) (hA : A ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k))
    (hD : ∀ x ∈ A, latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good x) :
    ∃ g : closedBall ((S (supportCellRoot μ R hR k z)).direction.orthogonalProjectionOnto (z : Ambient d))
        (3 * latticeRadius R k) → Ambient d,
      LipschitzWith ((activeProjectionGlobalLipschitzConstant d) ^ 2) g ∧
        Set.range f ∩ A ⊆ Set.range g := by
  let P := (S (supportCellRoot μ R hR k z)).direction
  obtain ⟨g, hgLip, _, _, hgRange⟩ := exists_affine_plane_disk_chart
    (S (supportCellRoot μ R hR k z)) (hS _).1 (P.orthogonalProjectionOnto (z : Ambient d))
    (3 * latticeRadius R k)
  let T := activeRegionTransitionMap μ R hR k z Good S hS 0 2
  have hTLip := activeRegionTransitionMap_global_lipschitz μ R hR k z Good S hS 0
    ε (by linarith) hfit 2
  have hr0 := latticeRadius_pos R hR k
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by linarith
  have hBm := mul_le_mul_of_nonneg_right hB hr0.le
  have hr2 : latticeRadius R (k + 2) = latticeRadius R k / 4096 := by
    rw [latticeRadius_add]
    norm_num
    ring
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) ((17039360 * ε) / 63) (by positivity)
    hmodel.2.2.2.1 A (latticeRadius R (k + 1)) hD 2 (by
      rw [hr2, latticeRadius_succ]
      nlinarith)
  refine ⟨T ∘ g, by simpa only [mul_one] using! hTLip.comp hgLip, ?_⟩
  intro x hx
  have hx2 : x ∈ activeRegionSurface μ R hR k z Good S hS (0 + 2) := (hstable ▸ hx).1
  rw [activeRegionSurface_add] at hx2
  obtain ⟨y, hy, hTy⟩ := hx2
  change T y = x at hTy
  have hmove := active_region_transition_surface_movement μ R hR k z Good S hS ε hε f hmodel 0 2 y hy
  change dist (T y) y ≤ (2 * ((17039360 * ε) / 63)) * latticeRadius R k at hmove
  rw [hTy] at hmove
  have hyz : dist y (z : Ambient d) ≤ 3 * latticeRadius R k := by
    have ht := dist_triangle y x (z : Ambient d)
    rw [dist_comm y x] at ht
    have hxz : dist x (z : Ambient d) ≤ 2 * latticeRadius R k := hA hx.2
    nlinarith
  have hproject := P.norm_starProjection_apply_le (y - (z : Ambient d))
  rw [map_sub, ← dist_eq_norm (P.starProjection y) (P.starProjection (z : Ambient d)),
    ← dist_eq_norm y (z : Ambient d)] at hproject
  have hyg : y ∈ Set.range g := by
    rw [hgRange]
    exact ⟨hy, hproject.trans hyz⟩
  obtain ⟨u, hu⟩ := hyg
  refine ⟨u, ?_⟩
  change T (g u) = x
  rw [hu]
  exact hTy

end

end RieszRectifiability

end OAI
