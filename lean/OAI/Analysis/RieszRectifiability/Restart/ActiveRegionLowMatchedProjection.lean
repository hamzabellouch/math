import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.ContinuousChartInnerCoverage
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionAllScaleForwardFlatness

namespace OAI

/-!
# Matched projections at low stopping scales

An active cell at the requested radius supplies a fitting direction with small
forward height error. Its limiting chart also covers a definite projected ball,
so both estimates hold for the same plane through the requested center.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_active_region_low_matched_projection {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 72057594037927936) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r)
    (hrtop : r ≤ latticeRadius R k / 2097152)
    (hD : cellRegionStoppingScale μ R hR k z Good p ≤ 16384 * r) :
    ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
      (∀ x ∈ Set.range f ∩ closedBall p (1024 * r),
        infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ (281474976710656 * ε) * r) ∧
      closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
        P.orthogonalProjectionOnto '' (Set.range f ∩ closedBall p (r / 16)) := by
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  obtain ⟨t, q, hqF, hqlo, hqhi, hnear⟩ := exists_active_cell_at_requested_radius
    μ R hR k z Good p (131072 * r) (by positivity) (by linarith) (by linarith)
  have hq := ((mem_activeLevelIndex μ R hR k z Good t q).mp hqF).2
  let P := (S q).direction
  let : Nonempty (S q) := (hS q).1.to_subtype
  have hpq : p ∈ closedBall q.center ((17 / 8 : ℝ) * q.radius) := by
    change dist p q.center ≤ (17 / 8 : ℝ) * q.radius
    nlinarith [q.radius_pos]
  have hpheight := active_region_limit_height_on_enlarged_active_ball μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel q hq p hp hpq
  obtain ⟨H, hH, hRange, hDisp, hHeight, _⟩ :=
    exists_active_region_limit_chart_with_normal_error μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel q hq
  have hroom : dist (P.orthogonalProjectionOnto p) (P.orthogonalProjectionOnto q.center) +
      2 * (r / 32) ≤ (5 / 2 : ℝ) * q.radius := by
    have hpj := P.norm_starProjection_apply_le (p - q.center)
    rw [map_sub] at hpj
    change dist (P.orthogonalProjectionOnto p) (P.orthogonalProjectionOnto q.center) ≤ dist p q.center at hpj
    nlinarith
  have hAreaBudget : (534000 * ε) * q.radius + (534000 * ε) * q.radius ≤ r / 32 := by
    have hcoeff : 1068000 * 134217728 * ε ≤ 1 / 32 := by nlinarith
    have hqr := mul_le_mul_of_nonneg_left hqhi hε.le
    have hrr := mul_le_mul_of_nonneg_right hcoeff hr.le
    nlinarith
  have hDispBudget : ((17039360 * ε) / 63) * q.radius ≤ r / 32 := by
    nlinarith [mul_pos hε q.radius_pos]
  have hProjected := continuous_chart_inner_projection_coverage (S q) (hS q).1
    (P.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius) H hH
    (Set.range f) hRange p (r / 32) (((17039360 * ε) / 63) * q.radius)
    ((534000 * ε) * q.radius) ((534000 * ε) * q.radius) (by positivity)
    hroom hDisp hHeight hpheight hDispBudget hAreaBudget
  rw [show 2 * (r / 32) = r / 16 by ring] at hProjected
  refine ⟨P, (hS q).2, ?_, hProjected⟩
  intro x hx
  have hxq : x ∈ closedBall q.center ((17 / 8 : ℝ) * q.radius) := by
    have ht := dist_triangle x p q.center
    have hxp : dist x p ≤ 1024 * r := hx.2
    change dist x q.center ≤ (17 / 8 : ℝ) * q.radius
    nlinarith
  have hxheight := active_region_limit_height_on_enlarged_active_ball μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel q hq x hx.1 hxq
  have hparallel := infDist_parallel_plane_through_point_le (S q) p x
  change infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ _ at hparallel
  nlinarith [mul_le_mul_of_nonneg_left hqhi hε.le, mul_pos hε hr]

end

end RieszRectifiability

end OAI
