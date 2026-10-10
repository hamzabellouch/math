import OAI.Geometry.CylinderCovering.Beams.StripDefinitions
import OAI.Geometry.CylinderCovering.Convexity.SimilarityDefinitions

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace
namespace CylinderCovering.BeamStrip

theorem IsRectangle.similarity_image {B : Set Space} (hB : IsRectangle B)
    (a : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    IsRectangle (Similarity.map a r L '' B) := by
  obtain ⟨c,u,v,huv,hu,hv,rfl⟩ := hB
  refine ⟨Similarity.map a r L c, r • L u, r • L v, ?_, ?_, ?_, ?_⟩
  · simp [inner_smul_left, inner_smul_right, L.inner_map_map, huv]
  · exact smul_ne_zero hr (fun h => hu (L.injective (by simpa using h)))
  · exact smul_ne_zero hr (fun h => hv (L.injective (by simpa using h)))
  · ext z
    constructor
    · rintro ⟨x, ⟨s,hs,t,ht,rfl⟩, rfl⟩
      refine ⟨s,hs,t,ht,?_⟩
      simp only [Similarity.map, map_add, map_smul]
      module
    · rintro ⟨s,hs,t,ht,rfl⟩
      refine ⟨c+s • u+t • v, ⟨s,hs,t,ht,rfl⟩, ?_⟩
      simp only [Similarity.map, map_add, map_smul]
      module

theorem IsRectangle.transportedBase {B : Set Space} (hB : IsRectangle B)
    (u a : Space) {r : ℝ} (hr : r ≠ 0) (L : Space ≃ₗᵢ[ℝ] Space) :
    IsRectangle (Similarity.transportedBase B u a r L) := by
  exact hB.similarity_image (Similarity.project (L u) a) hr L

end CylinderCovering.BeamStrip

end

end OAI
