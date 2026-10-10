import OAI.Combinatorics.Crossing.ParallelDirection
import Mathlib.Analysis.Convex.Basic

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem collinear_segment_subset_union (a b c : Plane) (hac : a ≠ c)
    (h : det2 (b-a) (c-b)=0) :
    segment ℝ a c ⊆ segment ℝ a b ∪ segment ℝ b c := by
  have hd : det2 (c-a) (b-a)=0 := by
    have he : det2 (c-a) (b-a) = -det2 (b-a) (c-b) := by dsimp [det2]; ring
    rw [he,h,neg_zero]
  have hp := vector_parallel_of_det_zero (c-a) (b-a) (sub_ne_zero.mpr (Ne.symm hac)) hd
  have hb : b ∈ Set.range (AffineMap.lineMap a c : ℝ → Plane) := by
    refine ⟨dot2 (c-a) (b-a)/squaredLength (c-a),?_⟩
    rw [AffineMap.lineMap_apply]
    change (dot2 (c-a) (b-a)/squaredLength (c-a)) • (c-a)+a=b
    rw [← hp,sub_add_cancel]
  intro x hx
  rw [← insert_endpoints_openSegment] at hx
  rcases hx with hxa | hxc | hxo
  · subst x
    exact Or.inl (left_mem_segment ℝ a b)
  · subst x
    exact Or.inr (right_mem_segment ℝ b c)
  · rcases openSegment_subset_union a c hb hxo with hxb | hx'
    · subst x
      exact Or.inl (right_mem_segment ℝ a b)
    · exact hx'.elim (fun hh => Or.inl (openSegment_subset_segment ℝ a b hh))
        (fun hh => Or.inr (openSegment_subset_segment ℝ b c hh))

end Zarankiewicz

end

end OAI
