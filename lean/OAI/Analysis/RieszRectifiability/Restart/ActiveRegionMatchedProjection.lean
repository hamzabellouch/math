import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveMatchedProjection
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLowMatchedProjection
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLargeMatchedProjection
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionHighMatchedProjection

namespace OAI

/-!
# Matched projection at every scale

The large-, high-, positive-, and low-stopping-scale constructions combine to
give one plane with a uniform forward flatness estimate and projected disk
coverage at every positive radius of an active-region limit surface.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_active_region_matched_projection_all_scales {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 72057594037927936) (hsmall : activeProjectionError d ε ≤ 1 / 4096)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r) :
    ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
      (∀ x ∈ Set.range f ∩ closedBall p (1024 * r),
        infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤
          (281474976710656 * (ε + activeProjectionError d ε)) * r) ∧
      closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
        P.orthogonalProjectionOnto '' (Set.range f ∩ closedBall p (r / 16)) := by
  have hη : 0 ≤ activeProjectionError d ε := by unfold activeProjectionError; positivity
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  have hweak : activeProjectionError d ε ≤ 1 / 128 := by linarith
  by_cases hlarge : latticeRadius R k / 2097152 ≤ r
  · obtain ⟨P, hP, hHeight, hCover⟩ := exists_active_region_large_matched_projection μ R hR k z Good S hS
      ε hε hεfine f hmodel p hp r hr hlarge
    refine ⟨P, hP, ?_, hCover⟩
    intro x hx
    exact (hHeight x hx).trans (mul_le_mul_of_nonneg_right (by nlinarith) hr.le)
  have hrsmall := (not_le.mp hlarge).le
  by_cases hhigh : latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good p
  · obtain ⟨P, hP, hHeight, hCover⟩ := exists_active_region_high_matched_projection μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel p hp r hr hrsmall hhigh
    refine ⟨P, hP, ?_, hCover⟩
    intro x hx
    exact (hHeight x hx).trans (mul_le_mul_of_nonneg_right (by nlinarith) hr.le)
  by_cases hnear : 1024 * r ≤ cellRegionStoppingScale μ R hR k z Good p / 16
  · have hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p := by linarith
    obtain ⟨P, hP, hHeight, hCover⟩ := exists_active_region_positive_matched_projection μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel p hp hDpos (not_le.mp hhigh) r hr hnear
    refine ⟨P, hP, ?_, hCover⟩
    intro x hx
    exact (hHeight x hx).trans (mul_le_mul_of_nonneg_right (by nlinarith) hr.le)
  obtain ⟨P, hP, hHeight, hCover⟩ := exists_active_region_low_matched_projection μ R hR k z Good S hS
    ε hε hεfine hweak hfit f hmodel p hp r hr hrsmall (by linarith [not_le.mp hnear])
  refine ⟨P, hP, ?_, hCover⟩
  intro x hx
  exact (hHeight x hx).trans (mul_le_mul_of_nonneg_right (by nlinarith) hr.le)

end

end RieszRectifiability

end OAI
