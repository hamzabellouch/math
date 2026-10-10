import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.NativeSurfaceRegularity
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionMatchedProjection

namespace OAI

/-!
# Geometry of the native area measure on a limit surface

Two-sided Hausdorff area bounds on a closed embedded active-region limit image
give regularity, exact support, AD regularity, and infinite support diameter for
its native area measure. Matched projection estimates then transfer to that
support with the same explicit flatness and disk-coverage constants.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

theorem active_region_native_surface_geometry {n d : ℕ} (hn : 0 < n)
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
    (hembed : IsClosedEmbedding f)
    (c C : ℝ≥0∞) (hc : 0 < c) (hcfin : c < ⊤) (hC : C < ⊤)
    (hlower : ∀ p ∈ Set.range f, ∀ r : ℝ, 0 < r →
      c * (ENNReal.ofReal r) ^ n ≤
        (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r))
    (hupper : ∀ (p : Ambient d) (r : ℝ), 0 < r →
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) ≤
        C * (ENNReal.ofReal r) ^ n) :
    let ν := nativeSurfaceArea n (Set.range f)
    ν.Regular ∧ ν.support = Set.range f ∧ ADRegular n ν ∧ ediam ν.support = ⊤ ∧
      1 ≤ nativeSurfaceADConstant n c C ∧
      GlobalUpperGrowth n (nativeSurfaceADConstant n c C) ν ∧
      (∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (r ^ n / nativeSurfaceADConstant n c C) ≤ ν (ball p r)) ∧
      ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
        ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
          (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
            infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤
              (281474976710656 * (ε + activeProjectionError d ε)) * r) ∧
          closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
            P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)) := by
  dsimp only
  have hclosed := hembed.isClosed_range
  have hs := nativeSurfaceArea_support (Set.range f) hclosed c hc hlower
  have hne : (Set.range f).Nonempty := by
    obtain ⟨a, ha⟩ := (hS (supportCellRoot μ R hR k z)).1
    exact ⟨f ⟨a, ha⟩, Set.mem_range_self _⟩
  obtain ⟨hK, hg, hl⟩ := nativeSurfaceArea_uniform_bounds (Set.range f) c C hc hcfin hC hlower hupper
  refine ⟨nativeSurfaceArea_regular _ C hC hupper, hs,
    nativeSurfaceArea_adRegular _ hclosed c C hc hcfin hC hlower hupper,
    nativeSurfaceArea_support_ediam_top hn _ hclosed hne c C hc hcfin hC hlower hupper,
    hK, hg, ?_, ?_⟩
  · intro p hp r hr
    exact hl p (hs ▸ hp) r hr
  · rw [hs]
    intro p hp r hr
    exact exists_active_region_matched_projection_all_scales μ R hR k z Good S hS
      ε hε hεfine hsmall hfit f hmodel p hp r hr

end

end RieszRectifiability

end OAI
