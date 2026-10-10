import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BoundedPlaneBoxes

namespace OAI

/-!
# Null boundaries of coordinate boxes

The frontier of an open coordinate box lies in the difference between its
closed and open versions. Their almost-everywhere equality for volume shows
that this frontier has measure zero.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem box_Ioo_frontier_volume_zero {ι : Type*} [Fintype ι] (I : Box ι) :
    (volume : Measure (ι → ℝ)) (frontier (Box.Ioo I)) = 0 := by
  have hopen : IsOpen (Box.Ioo I) := isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : frontier (Box.Ioo I) ⊆ Box.Icc I \ Box.Ioo I := by
    rw [hopen.frontier_eq]
    exact sdiff_subset_sdiff_left (closure_minimal I.Ioo_subset_Icc I.isCompact_Icc.isClosed)
  have heq : (Box.Icc I \ Box.Ioo I) =ᵐ[volume] (∅ : Set (ι → ℝ)) := by
    filter_upwards [I.Ioo_ae_eq_Icc] with x hx
    apply propext
    change (x ∈ Box.Icc I ∧ x ∉ Box.Ioo I) ↔ False
    have hx' : x ∈ Box.Ioo I ↔ x ∈ Box.Icc I := iff_of_eq hx
    tauto
  exact measure_mono_null hsub ((measure_congr heq).trans measure_empty)

theorem exhaustionBox_Icc_dist_zero_le {ι : Type*} [Fintype ι] (H : ℕ) (u : ι → ℝ)
    (hu : u ∈ Box.Icc (exhaustionBox ι H)) : dist u 0 ≤ (H : ℝ) + 1 := by
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ H + 1)).mpr
  intro i
  have hi : -((H : ℝ) + 1) ≤ u i ∧ u i ≤ (H : ℝ) + 1 := ⟨hu.1 i, hu.2 i⟩
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using! abs_le.mpr hi

theorem exhaustionBox_Icc_image_mem_outerBall {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (K : ℝ≥0) (he : LipschitzWith K e)
    (H : ℕ) (u : ι → ℝ) (hu : u ∈ Box.Icc (exhaustionBox ι H)) :
    e u ∈ ball (e 0) (planeBoxOuterRadius K H) := by
  apply mem_ball.mpr
  have hdist := (he.dist_le_mul u 0).trans
    (mul_le_mul_of_nonneg_left (exhaustionBox_Icc_dist_zero_le H u hu) K.coe_nonneg)
  dsimp [planeBoxOuterRadius]
  nlinarith

theorem boundedProjectionRegion_preimage_frontier_subset {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e) (H : ℕ) :
    e ⁻¹' frontier (boundedProjectionRegion π (e 0) K H) ⊆
      frontier (Box.Ioo (exhaustionBox ι H)) := by
  intro u hu
  have hsplit := frontier_inter_subset (openProjectionBox (exhaustionBox ι H) π)
    (ball (e 0) (planeBoxOuterRadius K H)) hu
  rcases hsplit with hA | hB
  · have h := hπ.frontier_preimage_subset (Box.Ioo (exhaustionBox ι H)) hA.1
    simpa only [mem_preimage, hleft u] using! h
  · have hclos : closure (openProjectionBox (exhaustionBox ι H) π) ⊆
        π ⁻¹' Box.Icc (exhaustionBox ι H) :=
      closure_minimal (fun _ hx => (exhaustionBox ι H).Ioo_subset_Icc hx)
        ((exhaustionBox ι H).isCompact_Icc.isClosed.preimage hπ)
    have hucc : u ∈ Box.Icc (exhaustionBox ι H) := by
      simpa only [mem_preimage, hleft u] using! hclos hB.1
    have hin := exhaustionBox_Icc_image_mem_outerBall e K he H u hucc
    have hout := hB.2
    rw [isOpen_ball.frontier_eq] at hout
    exact False.elim (hout.2 hin)

theorem boundedProjectionRegion_null_frontier {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e) (H : ℕ) :
    coordinatePlaneMeasure e (frontier (boundedProjectionRegion π (e 0) K H)) = 0 := by
  rw [coordinatePlaneMeasure, Measure.map_apply he.continuous.measurable isClosed_frontier.measurableSet]
  exact measure_mono_null (boundedProjectionRegion_preimage_frontier_subset e π K he hπ hleft H)
    (box_Ioo_frontier_volume_zero (exhaustionBox ι H))

theorem boundedProjectionRegion_compact_closure {ι : Type*} {d : ℕ}
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    IsCompact (closure (boundedProjectionRegion π a K H)) := by
  apply (isCompact_closedBall a (planeBoxOuterRadius K H)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  exact fun _ hx => mem_closedBall.mpr hx.2.le

end

end RieszRectifiability

end OAI
