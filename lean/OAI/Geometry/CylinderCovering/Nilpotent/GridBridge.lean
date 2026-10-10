import OAI.Geometry.CylinderCovering.Nilpotent.SmoothRateDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.GridMeasure
import OAI.Geometry.CylinderCovering.Physical.WeightLipschitz

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CylinderCovering.NilpotentRate

lemma compact_coordinate_bound {D : Set Plane} (hD : IsCompact D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B := by
  obtain ⟨C, hC⟩ := hD.isBounded.exists_norm_le
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x hx
  constructor
  · have h0 : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    exact h0.trans ((hC x hx).trans (le_max_right _ _))
  · have h1 : |x 1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 1
    exact h1.trans ((hC x hx).trans (le_max_right _ _))

lemma coarseIndices_eq_finset {δ B : ℝ} {D : Set Plane}
    (hδ : 0 < δ) (hbound : ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B) :
    coarseIndices δ D = (NilpotentGrid.coarseIndices δ B D : Set Index) := by
  ext i
  change (cell δ i ∩ D).Nonempty ↔ i ∈ NilpotentGrid.coarseIndices δ B D
  rw [NilpotentGrid.mem_coarseIndices_iff hδ hbound]
  rw [inter_comm]
  rfl

lemma gridUnion_eq_coarseUnion {δ B : ℝ} {D : Set Plane}
    (hδ : 0 < δ) (hbound : ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B) :
    gridUnion δ D = NilpotentGrid.coarseUnion δ B D := by
  simp only [gridUnion, coarseIndices_eq_finset hδ hbound, Finset.mem_coe,
    NilpotentGrid.coarseUnion, cell]

lemma coarseIndices_finite {δ : ℝ} {D : Set Plane}
    (hδ : 0 < δ) (hD : IsCompact D) : (coarseIndices δ D).Finite := by
  obtain ⟨B, _, hB⟩ := compact_coordinate_bound hD
  rw [coarseIndices_eq_finset hδ hB]
  exact Finset.finite_toSet _

lemma gridUnion_isCompact {δ : ℝ} {D : Set Plane}
    (hδ : 0 < δ) (hD : IsCompact D) : IsCompact (gridUnion δ D) := by
  obtain ⟨B, _, hB⟩ := compact_coordinate_bound hD
  rw [gridUnion_eq_coarseUnion hδ hB]
  exact NilpotentGrid.coarseUnion_isCompact δ B D

lemma gridUnion_contains {δ : ℝ} {D : Set Plane}
    (hδ : 0 < δ) (hD : IsCompact D) : D ⊆ gridUnion δ D := by
  obtain ⟨B, _, hB⟩ := compact_coordinate_bound hD
  rw [gridUnion_eq_coarseUnion hδ hB]
  exact NilpotentGrid.subset_coarseUnion hδ hB

lemma gridUnion_near {δ : ℝ} {D : Set Plane} {x : Plane}
    (hδ : 0 < δ) (hD : IsCompact D) (hx : x ∈ gridUnion δ D) :
    ∃ y ∈ D, ‖x-y‖ ≤ Real.sqrt 2 * δ := by
  obtain ⟨B, _, hB⟩ := compact_coordinate_bound hD
  rw [gridUnion_eq_coarseUnion hδ hB] at hx
  exact NilpotentGrid.coarseUnion_near hδ.le hx

lemma retained_center_tag_distance {δ R : ℝ} {D : Set Plane}
    {tag : Index → Plane} {Q : Index → Plane ≃ₗᵢ[ℝ] Plane} {i j : Index}
    (hδ : 0 ≤ δ) (htag : tag i ∈ cell δ i)
    (hret : (i,j) ∈ retainedIndices δ R D Q) :
    ‖fineCenter δ (Q i) j - tag i‖ ≤ R + Real.sqrt 2 * δ := by
  obtain ⟨y, hy, heq⟩ := (NilpotentGrid.coarseCell_isCompact δ i).exists_infDist_eq_dist
    ⟨tag i, htag⟩ (fineCenter δ (Q i) j)
  have hdist : ‖fineCenter δ (Q i) j - y‖ ≤ R := by
    rw [← dist_eq_norm, ← heq]
    exact hret.2
  calc
    ‖fineCenter δ (Q i) j - tag i‖ ≤
        ‖fineCenter δ (Q i) j - y‖ + ‖y - tag i‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ R + Real.sqrt 2 * δ := add_le_add hdist (NilpotentGrid.same_cell_distance hδ hy htag)

lemma retained_weight_error {δ M K h : ℝ} {D : Set Plane} {G : Plane → Plane}
    {tag : Index → Plane} {Q : Index → Plane ≃ₗᵢ[ℝ] Plane} {i j : Index}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (htag : tag i ∈ cell δ i) (hA : ‖fderiv ℝ G (tag i)‖ ≤ M)
    (hret : (i,j) ∈ retainedIndices δ (collarRadius M K δ) D Q) :
    |RuledApproximation.physicalWeight h
      (affineVelocity G tag i (fineCenter δ (Q i) j)) -
      RuledApproximation.physicalWeight h (G (tag i))| ≤
      max 1 |h| * M * ((1 + M) * (Real.sqrt 2 + K) + Real.sqrt 2) * δ := by
  have hnear := retained_center_tag_distance hδ htag hret
  have hC : 0 ≤ (1 + M) * (Real.sqrt 2 + K) := by positivity
  have hsq : δ ^ 2 ≤ δ := by nlinarith only [hδ, hδ1]
  have hm := mul_le_mul_of_nonneg_left hsq hC
  have hl : ‖fineCenter δ (Q i) j - tag i‖ ≤
      ((1 + M) * (Real.sqrt 2 + K) + Real.sqrt 2) * δ := by
    unfold collarRadius at hnear
    nlinarith only [hnear, hm]
  exact RuledApproximation.affine_physicalWeight_error (fderiv ℝ G (tag i))
    hM (by positivity) hδ hA hl

end CylinderCovering.NilpotentRate

end

end OAI
