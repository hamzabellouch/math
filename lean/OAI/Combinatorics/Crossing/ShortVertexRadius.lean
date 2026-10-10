import OAI.Combinatorics.Crossing.VertexSpokeBounds

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exists_short_vertex_radius {m n : ℕ} (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ e,
      4*r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      4*r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)) := by
  obtain ⟨s,hs,hsρ,hbound⟩ := exists_vertex_spoke_bound D P hmin ρ hρ
  refine ⟨s/2,by positivity,by linarith,?_⟩
  intro e
  obtain ⟨hfirst,hlast⟩ := hbound e
  constructor <;> nlinarith

end Zarankiewicz

end

end OAI
