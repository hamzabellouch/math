import OAI.Combinatorics.Crossing.FiniteIntersectionDrawing
import OAI.Combinatorics.Crossing.CrossingIncidence
import OAI.Combinatorics.Crossing.PathSubarc

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def drawingMarks (D : FiniteIntersectionDrawing m n) : Set Plane :=
  Set.range D.vertex ∪ crossingPoints D.toContinuousDrawing

theorem drawingMarks_finite (D : FiniteIntersectionDrawing m n) : (drawingMarks D).Finite :=
  (Set.finite_range D.vertex).union D.crossings_finite

theorem crossing_not_vertex (D : FiniteIntersectionDrawing m n) (x : Plane)
    (hx : x ∈ crossingPoints D.toContinuousDrawing) (v : BipartiteVertex m n) : x ≠ D.vertex v := by
  obtain ⟨e,f,hef,⟨t,ht,he⟩,hf⟩ := hx
  intro hh
  exact D.interior_avoids_vertices e t ht v (he.trans hh)

theorem marked_parameters_finite (D : FiniteIntersectionDrawing m n) (e : BipartiteEdge m n) :
    ((D.edge e) ⁻¹' drawingMarks D).Finite :=
  Set.Finite.preimage (D.edge_injective e).injOn (drawingMarks_finite D)

theorem marked_parameter_zero (D : FiniteIntersectionDrawing m n) (e : BipartiteEdge m n) :
    (0 : unitInterval) ∈ (D.edge e) ⁻¹' drawingMarks D := by
  exact Or.inl ⟨.inl e.1,(D.edge e).source.symm⟩

theorem marked_parameter_one (D : FiniteIntersectionDrawing m n) (e : BipartiteEdge m n) :
    (1 : unitInterval) ∈ (D.edge e) ⁻¹' drawingMarks D := by
  exact Or.inl ⟨.inr e.2,(D.edge e).target.symm⟩

theorem unmarked_edge_point_interior (D : FiniteIntersectionDrawing m n) (e : BipartiteEdge m n)
    (t : unitInterval) (ht : D.edge e t ∉ drawingMarks D) : t ∈ Set.Ioo (0 : unitInterval) 1 := by
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    exact ht (marked_parameter_zero D e)
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    exact ht (marked_parameter_one D e)
  exact ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩

theorem unmarked_intersection_same_edge (D : FiniteIntersectionDrawing m n)
    (e f : BipartiteEdge m n) (s t : unitInterval)
    (he : D.edge e s=D.edge f t) (hs : D.edge e s ∉ drawingMarks D) : e=f := by
  by_contra hef
  have hsi := unmarked_edge_point_interior D e s hs
  have hti := unmarked_edge_point_interior D f t (he ▸ hs)
  exact hs (Or.inr ⟨e,f,hef,⟨s,hsi,rfl⟩,⟨t,hti,he.symm⟩⟩)

end Zarankiewicz

end

end OAI
