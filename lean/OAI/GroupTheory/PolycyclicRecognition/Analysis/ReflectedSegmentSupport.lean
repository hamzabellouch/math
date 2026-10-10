import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateSymmetries

namespace OAI

/-! # The exponent gain from two reflected segments

The reflection-doubling identity follows from finite balanced support data
and gives the support gain for a pair of reflected segments.
-/

noncomputable section
namespace PolycyclicRecognition.SupportDatum

open Set

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

omit [FiniteDimensional ℝ W] in
private theorem compact_segment (w : W) : IsCompact (segment ℝ 0 w) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
    (continuous_id.smul continuous_const))

omit [Nonempty B] in
theorem weightSupport_union {E F : Set W} (hE : IsCompact E) (hneE : E.Nonempty)
    (hF : IsCompact F) (hneF : F.Nonempty) (i : I) :
    D.weightSupport (E ∪ F) i = max (D.weightSupport E i) (D.weightSupport F i) := by
  obtain ⟨x, hx, he⟩ := D.exists_weightSupport_point hE hneE i
  obtain ⟨y, hy, hf⟩ := D.exists_weightSupport_point hF hneF i
  obtain ⟨z, hz, hu⟩ := D.exists_weightSupport_point (hE.union hF)
    (hneE.mono subset_union_left) i
  apply le_antisymm
  · rw [hu]
    rcases hz with hz | hz
    · exact (D.weight_le_weightSupport hE hz i).trans (le_max_left _ _)
    · exact (D.weight_le_weightSupport hF hz i).trans (le_max_right _ _)
  · apply max_le
    · rw [he]
      exact D.weight_le_weightSupport (hE.union hF) (Or.inl hx) i
    · rw [hf]
      exact D.weight_le_weightSupport (hE.union hF) (Or.inr hy) i

omit [Nonempty B] in
theorem weightSupport_opposite_segments (w : W) (i : I) :
    D.weightSupport (segment ℝ 0 w ∪ segment ℝ 0 (-w)) i =
      max 0 (D.weight i w) + max 0 (D.weight i (-w)) := by
  rw [D.weightSupport_union (compact_segment w) ⟨0, left_mem_segment ..⟩
    (compact_segment (-w)) ⟨0, left_mem_segment ..⟩,
    D.weightSupport_segment, D.weightSupport_segment, map_neg]
  rcases le_total 0 (D.weight i w) with h | h
  · simp [h]
  · simp [h]

omit [Nonempty B] in
theorem basisTemplateSupport_opposite_segments (w : W) (b : B) :
    D.basisTemplateSupport (segment ℝ 0 w ∪ segment ℝ 0 (-w)) b =
      2 * D.basisSupport b w := by
  simp only [basisTemplateSupport, D.weightSupport_opposite_segments,
    mul_add, Finset.sum_add_distrib]
  change D.basisSupport b w + D.basisSupport b (-w) = _
  rw [D.basisSupport_neg]
  ring

theorem templateSupport_opposite_segments (w : W) :
    D.templateSupport (segment ℝ 0 w ∪ segment ℝ 0 (-w)) =
      2 * D.segmentSupport w := by
  apply le_antisymm
  · apply D.templateSupport_le
    intro b
    rw [D.basisTemplateSupport_opposite_segments]
    exact mul_le_mul_of_nonneg_left (D.basisSupport_le b w) (by norm_num)
  · obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun b => D.basisSupport b w)
    change 2 * Finset.univ.sup' _ _ ≤ _
    rw [hb, ← D.basisTemplateSupport_opposite_segments]
    exact D.basisTemplateSupport_le _ b

/-- Opposite images have twice the single-segment volume exponent. -/
theorem reflected_segment_support
    (A C : PolycyclicRecognition.templateSymmetryGroup D) {w : W}
    (hw : w ≠ 0) (hreflect : C.val w = -A.val w) :
    D.templateSupport (A.val '' segment ℝ 0 w) = D.segmentSupport w ∧
    D.templateSupport (C.val '' segment ℝ 0 w) = D.segmentSupport w ∧
    D.templateSupport ((A.val '' segment ℝ 0 w) ∪ (C.val '' segment ℝ 0 w)) =
      2 * D.segmentSupport w ∧ 0 < D.segmentSupport w := by
  have him (L : W ≃ₗ[ℝ] W) : L '' segment ℝ 0 w = segment ℝ 0 (L w) := by
    change L.toLinearMap.toAffineMap '' segment ℝ 0 w = _
    rw [image_segment]
    simp
  have ha := A.property (segment ℝ 0 w) (compact_segment w)
    ⟨0, left_mem_segment ..⟩ (convex_segment 0 w)
  have hc := C.property (segment ℝ 0 w) (compact_segment w)
    ⟨0, left_mem_segment ..⟩ (convex_segment 0 w)
  rw [D.templateSupport_segment] at ha hc
  refine ⟨ha, hc, ?_, D.segmentSupport_pos hw⟩
  rw [him A.val, him C.val, hreflect, D.templateSupport_opposite_segments]
  rw [him A.val, D.templateSupport_segment] at ha
  rw [ha]

end PolycyclicRecognition.SupportDatum

end

end OAI
