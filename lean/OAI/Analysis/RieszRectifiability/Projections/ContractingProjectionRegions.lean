import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.MatchedSurfaceCellPlanes
import OAI.Analysis.RieszRectifiability.Projections.ProjectionRegionAreaContraction
import OAI.Analysis.RieszRectifiability.Projections.ProjectionRegionThresholds

namespace OAI

/-!
# Contracting projection regions

Local surface flatness and projection coverage select a stopping region whose
representatives are quantitatively separated by projection. The core-area and
stop-shadow estimates control the mass of its stopping cells.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem exists_contracting_projection_region {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (σ κ : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hwidth : σ + κ ≤ 1) (hsmall : 2048 * σ * (κ + 1) ≤ κ)
    (hshadow : projectionStopShadowConstant n C σ κ ≤ nativeCoreAreaFraction n G)
    (hgeometry : ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
          infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ σ * r) ∧
        closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
          P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius ν (latticeRadius R k / 8))
    (z : (supportLatticeNets ν R hR k).points) :
    ∃ Good : SupportCellDescendant ν R hR k z → Prop,
      (∀ i : SupportCellDescendant ν R hR k z, i.depth = 0 → Good i) ∧
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ cellRegionRepresentatives ν R hR k z Good,
          ∀ y ∈ cellRegionRepresentatives ν R hR k z Good,
            dist x y ≤ (2 / κ) * dist (P.starProjection x) (P.starProjection y)) ∧
        ENNReal.ofReal (nativeCoreAreaFraction n G) * ν (cleanSupportCell ν R hR k z) ≤
          ν (cellRegionLimit ν R hR k z Good) ∧
        (∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell) ≤
          ENNReal.ofReal (1 - nativeCoreAreaFraction n G) * ν (cleanSupportCell ν R hR k z) := by
  obtain ⟨S, hS, hcenter, hfit, hcover⟩ := exists_matched_surface_cell_planes ν σ hgeometry R hR k z
  let P := (S (supportCellRoot ν R hR k z)).direction
  let Good := cellProjectionNoncollapse S P κ
  have hroot : ∀ i : SupportCellDescendant ν R hR k z, i.depth = 0 → Good i :=
    cellProjectionNoncollapse_root ν R hR k z S κ hκ1
  have hdim : Module.finrank ℝ P = n := (hS (supportCellRoot ν R hR k z)).2
  obtain ⟨T, hnorm, hT, hdisks⟩ := exists_projection_disk_coordinates P hdim
  have hTcover := hdisks (ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16))
    z (latticeRadius R k / 32) hcover
  obtain ⟨hretain, hcontract⟩ := projection_region_original_area_contraction ν A hν hsupport C G hC hG
    hg hlower R hR k hcore z S hS hcenter P σ κ hσ hκ.le hwidth hfit T hT hnorm hTcover hshadow
  refine ⟨Good, hroot, P, hdim, ?_, hretain, hcontract⟩
  apply projection_separates_noncollapsing_region_representatives ν R hR k z Good hroot P σ κ
    hσ.le hκ hsmall
  intro i hi
  exact ⟨S i, hS i, fun w hw hνw => hfit i w ⟨hνw, ball_subset_closedBall hw⟩, hi⟩

end

end RieszRectifiability

end OAI
