import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.ProjectionConditionedRegions

namespace OAI

/-!
# Matched planes for support-cell descendants

Pointwise geometric fits select an affine plane through every descendant center.
The root plane retains the projected disk coverage supplied by the same choice.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_matched_surface_cell_planes {n d : ℕ}
    (ν : Measure (Ambient d)) (σ : ℝ)
    (hgeometry : ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
          infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ σ * r) ∧
        closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
          P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points) :
    ∃ S : SupportCellDescendant ν R hR k z → AffineSubspace ℝ (Ambient d),
      (∀ i, IsAffineNPlane n (S i)) ∧ (∀ i, i.center ∈ S i) ∧
      (∀ i, ∀ x ∈ ν.support ∩ closedBall i.center (1024 * i.radius),
        infDist x (S i : Set (Ambient d)) ≤ σ * i.radius) ∧
      let P := (S (supportCellRoot ν R hR k z)).direction
      closedBall (P.orthogonalProjectionOnto z) (latticeRadius R k / 32) ⊆
        P.orthogonalProjectionOnto '' (ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16)) := by
  classical
  have hall (i : SupportCellDescendant ν R hR k z) :=
    hgeometry i.center i.center_mem_support i.radius i.radius_pos
  choose Ps hdim hfit hcover using hall
  let S (i : SupportCellDescendant ν R hR k z) := AffineSubspace.mk' i.center (Ps i)
  have hS : ∀ i, IsAffineNPlane n (S i) := by
    intro i
    refine ⟨AffineSubspace.mk'_nonempty i.center (Ps i), ?_⟩
    rw [AffineSubspace.direction_mk']
    exact hdim i
  refine ⟨S, hS, ?_, hfit, ?_⟩
  · intro i
    apply AffineSubspace.mem_mk'.mpr
    simpa only [vsub_self] using! (Ps i).zero_mem
  · change closedBall ((S (supportCellRoot ν R hR k z)).direction.orthogonalProjectionOnto z) _ ⊆ _
    dsimp only [S]
    rw [AffineSubspace.direction_mk']
    exact hcover (supportCellRoot ν R hR k z)

end

end RieszRectifiability

end OAI
