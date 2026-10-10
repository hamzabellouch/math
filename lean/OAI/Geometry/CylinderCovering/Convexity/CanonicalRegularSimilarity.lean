import OAI.Geometry.CylinderCovering.Convexity.RegularSimplexSimilarity
import OAI.Geometry.TriangularCovering.Main
import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

noncomputable section
open Set
namespace CylinderCovering

theorem regularTetrahedron_similarity {K : Set Space} (hK : IsRegularTetrahedron K) :
    ∃ (t : Space) (r : ℝ) (L : Space ≃ₗᵢ[ℝ] Space),
      0 < r ∧ K = Similarity.map t r L '' TriangularCovering.K := by
  rcases hK with ⟨v, hv, a, ha, hd, rfl⟩
  obtain ⟨L, t, h⟩ := RegularSimplexSimilarity.regular_simplex_similarity
    TriangularCovering.tetraVertices v TriangularCovering.tetra_affineIndependent hv
    (by norm_num : (0 : ℝ) < 2) ha
    (fun _ _ hij => TriangularCovering.tetra_edge_length hij) hd
  refine ⟨t, a / 2, L, div_pos ha (by norm_num), ?_⟩
  rw [← TriangularCovering.K_eq_convexHull] at h
  exact h

end CylinderCovering

end

end OAI
