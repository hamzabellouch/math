import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveScaleBallSelection
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleProjectionCharts
import OAI.Analysis.RieszRectifiability.Surfaces.ChartNormalCone
import OAI.Analysis.RieszRectifiability.Flatness.GreedyAffineAnchors

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

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

theorem exists_active_region_positive_scale_normal_cone
    (p : Ambient d)
    (hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p)
    (hDsmall : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + 1)) :
    ∃ q : SupportCellDescendant μ R hR k z, activeRegionCell Good q ∧
      ∀ x ∈ Set.range f ∩ closedBall p (cellRegionStoppingScale μ R hR k z Good p / 16),
      ∀ y ∈ Set.range f ∩ closedBall p (cellRegionStoppingScale μ R hR k z Good p / 16),
        ‖((S q).directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
          (64768 * activeProjectionError d ε) * dist x y := by
  obtain ⟨q, hq, hqhi, hqlo, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good p hDpos hDsmall
  obtain ⟨hball, hscale⟩ := active_stopping_ball_chart_geometry μ R hR k z Good p q hqhi hqlo hnear
  obtain ⟨H, _, hSep, _, hNormal, _, _, hCover⟩ :=
    exists_active_region_positive_scale_projection_chart μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel q hq
      (closedBall p (cellRegionStoppingScale μ R hR k z Good p / 16)) hball hscale
  refine ⟨q, hq, ?_⟩
  intro x hx y hy
  have h := normal_projection_bound_on_chart_range (S q).direction H
    (Real.toNNReal (1012 * activeProjectionError d ε)) 64 hNormal hSep
    x (hCover hx) y (hCover hy)
  have hη : 0 ≤ activeProjectionError d ε := by unfold activeProjectionError; positivity
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), NNReal.coe_ofNat] at h
  nlinarith

theorem exists_active_region_positive_scale_centered_plane
    (p : Ambient d) (hp : p ∈ Set.range f)
    (hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p)
    (hDsmall : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + 1)) :
    ∃ W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n W ∧ p ∈ W ∧
      ∀ r : ℝ, 0 < r → r ≤ cellRegionStoppingScale μ R hR k z Good p / 16 →
        ∀ x ∈ Set.range f ∩ closedBall p r,
          infDist x (W : Set (Ambient d)) ≤ (64768 * activeProjectionError d ε) * r := by
  obtain ⟨q, _, hcone⟩ := exists_active_region_positive_scale_normal_cone μ R hR k z
    Good S hS ε hε hεtiny hsmall hfit f hmodel p hDpos hDsmall
  let P := (S q).direction
  let W := AffineSubspace.mk' p P
  have hW : IsAffineNPlane n W := by
    refine ⟨AffineSubspace.mk'_nonempty p P, ?_⟩
    rw [AffineSubspace.direction_mk']
    exact (hS q).2
  have hpW : p ∈ W := by
    apply AffineSubspace.mem_mk'.mpr
    simpa only [vsub_self] using! P.zero_mem
  refine ⟨W, hW, hpW, ?_⟩
  intro r hr hrsmall x hx
  have hpA : p ∈ Set.range f ∩
      closedBall p (cellRegionStoppingScale μ R hR k z Good p / 16) :=
    ⟨hp, mem_closedBall_self (by positivity)⟩
  have hxA := (closedBall_subset_closedBall hrsmall (x := p)) hx.2
  have h := hcone x ⟨hx.1, hxA⟩ p hpA
  have hη : 0 ≤ activeProjectionError d ε := by unfold activeProjectionError; positivity
  rw [infDist_affine_translate p x P, submodule_infDist_eq_normal_projection]
  exact h.trans (mul_le_mul_of_nonneg_left hx.2 (by positivity))

end

end RieszRectifiability

end OAI
