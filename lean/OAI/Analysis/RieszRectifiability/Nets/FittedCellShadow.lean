import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.ProjectionDiskCoordinates
import OAI.Analysis.RieszRectifiability.Projections.ProjectionConditionedRegions
import OAI.Analysis.RieszRectifiability.Flatness.ContractedAffineHausdorffPatch

namespace OAI

/-!
An affine fit places a lattice cell in a thin neighborhood of a plane.
Contraction along one plane direction bounds the Hausdorff measure of the cell's image.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem fitted_cell_contracted_shadow_bound {n d : ℕ}
    (ν : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets ν R hR k).points)
    (i : SupportCellDescendant ν R hR k z)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hcenter : i.center ∈ S)
    (σ κ : ℝ) (hσ : 0 < σ) (hκ : 0 ≤ κ) (hwidth : σ + κ ≤ 1)
    (hfit : ∀ x ∈ ν.support ∩ closedBall i.center (1024 * i.radius),
      infDist x (S : Set (Ambient d)) ≤ σ * i.radius)
    (T : Ambient d →L[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (u : S.direction) (hu : ‖u‖ = 1) (hTu : ‖T (u : Ambient d)‖ ≤ κ) :
    (μH[(n : ℝ)] : Measure (Ambient n)) (T '' i.cell) ≤
      ENNReal.ofReal (((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
        (σ + κ) * (2 * i.radius) ^ n) := by
  have hcell : i.cell ⊆ closedBall i.center (2 * i.radius) :=
    sdiff_subset.trans (supportLatticeCell_bounds ν R hR (k + i.depth) ⟨i.center, i.mem_net⟩).2
  have hheight : ∀ x ∈ i.cell, infDist x (S : Set (Ambient d)) < 2 * σ * i.radius := by
    intro x hx
    have hxν := supportLatticeCell_subset_support ν R hR (k + i.depth)
      ⟨i.center, i.mem_net⟩ hx.1
    have hball : x ∈ closedBall i.center (1024 * i.radius) := by
      exact closedBall_subset_closedBall (by nlinarith [i.radius_pos]) (hcell hx)
    have h := hfit x ⟨hxν, hball⟩
    nlinarith [mul_pos hσ i.radius_pos]
  have h := contracted_affine_patch_hausdorff_image_bound S hS T.toLinearMap hT u hu κ hκ hTu
    i.center i.center hcenter i.cell (2 * i.radius) 0 (2 * i.radius) (2 * σ * i.radius)
    hcell (by simp) (by linarith) hheight (by nlinarith [i.radius_pos])
    (by nlinarith [mul_pos hσ i.radius_pos])
    (by nlinarith [mul_le_mul_of_nonneg_right hwidth i.radius_pos.le])
  have heq : (2 * σ * i.radius + κ * (2 * i.radius)) / (2 * i.radius) = σ + κ := by
    field_simp [ne_of_gt i.radius_pos]
  simpa only [heq] using! h

theorem projection_conditioned_cell_shadow_bound {n d : ℕ}
    (ν : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets ν R hR k).points)
    (S : SupportCellDescendant ν R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (hcenter : ∀ i, i.center ∈ S i)
    (P : Submodule ℝ (Ambient d)) (σ κ : ℝ)
    (hσ : 0 < σ) (hκ : 0 ≤ κ) (hwidth : σ + κ ≤ 1)
    (hfit : ∀ i, ∀ x ∈ ν.support ∩ closedBall i.center (1024 * i.radius),
      infDist x (S i : Set (Ambient d)) ≤ σ * i.radius)
    (T : Ambient d →L[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hnorm : ∀ x, ‖T x‖ = ‖P.starProjection x‖)
    (i : cellRegionStops ν R hR k z (cellProjectionNoncollapse S P κ)) :
    (μH[(n : ℝ)] : Measure (Ambient n)) (T '' i.val.cell) ≤
      ENNReal.ofReal (((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
        (σ + κ) * (2 * i.val.radius) ^ n) := by
  obtain ⟨u, hu, hPu⟩ := projection_conditioned_stop_contracted_unit ν R hR k z S P κ i.val i.property
  exact fitted_cell_contracted_shadow_bound ν R hR k z i.val (S i.val) (hS i.val) (hcenter i.val)
    σ κ hσ hκ hwidth (hfit i.val) T hT u hu (by rw [hnorm]; exact hPu.le)

end

end RieszRectifiability

end OAI
