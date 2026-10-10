import OAI.Geometry.CylinderCovering.Beams.RectangleSimilarity
import OAI.Geometry.CylinderCovering.Ruled.Similarity

namespace OAI

noncomputable section
open Set
namespace CylinderCovering.BeamStrip

theorem HasRectangularBase.similarity {C : RuledApproximation.Cylinder}
    (hC : HasRectangularBase C) (a : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) : HasRectangularBase (C.similarity a hr L) := by
  unfold HasRectangularBase
  change IsRectangle (Subtype.val ''
    (RuledApproximation.similarityPlaneMap C.axis C.unit_axis a hr L '' C.base))
  rw [RuledApproximation.similarityPlaneMap_image]
  exact hC.transportedBase C.axis a hr L

theorem mixed_finiteCover_similarity {K : Set Space} {A : ℝ}
    (h : RuledApproximation.HasFiniteCover
      (fun C => C.triangle ∨ HasRectangularBase C) K A)
    (a : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    RuledApproximation.HasFiniteCover
      (fun C => C.triangle ∨ HasRectangularBase C)
      (Similarity.map a r L '' K) (r^2*A) := by
  obtain ⟨n,C,hshape,hcover,hcost⟩ := h
  refine ⟨n,fun i => (C i).similarity a hr L,?_,
    RuledApproximation.similarity_cover C K hcover a hr L,?_⟩
  · intro i
    rcases hshape i with ht | hrct
    · exact Or.inl (RuledApproximation.Cylinder.similarity_triangle ht a hr L)
    · exact Or.inr (hrct.similarity a hr L)
  · rw [RuledApproximation.similarity_familyArea]
    exact mul_le_mul_of_nonneg_left hcost (sq_nonneg r)

end CylinderCovering.BeamStrip

end

end OAI
