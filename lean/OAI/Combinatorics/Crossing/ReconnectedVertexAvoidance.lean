import OAI.Combinatorics.Crossing.ReconnectedPaths
import OAI.Combinatorics.Crossing.CutVertexAvoidance
import OAI.Combinatorics.Crossing.ReconnectionVertexAvoidance

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem path_interior_avoids_vertices_of_range {V : Type*} (vertex : V → Plane) (a b : V)
    (γ : Path (vertex a) (vertex b)) (hinj : Function.Injective γ)
    (hrange : ∀ v, vertex v ∈ Set.range γ → v=a ∨ v=b)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (v : V) : γ t ≠ vertex v := by
  intro he
  rcases hrange v ⟨t,he⟩ with rfl | rfl
  · exact ht.1.ne (hinj (he.trans γ.source.symm)).symm
  · exact ht.2.ne (hinj (he.trans γ.target.symm))

theorem reconnectedForwardPath_vertex_eq (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (j : BipartiteVertex m n) (hj : D'.vertex j ∈ Set.range (reconnectedForwardPath Kp Kq hm)) :
    j=.inl p.1.1 ∨ j=.inr q.1.2 := by
  rcases reconnectedForwardPath_trace Kp Kq hm hj with (hj | hj) | hj
  · exact Or.inl (Kp.prefix_vertex_eq j hj)
  · exact False.elim (C.reconnection_segment_avoids_vertices p q hm D'.vertex hv true j hj)
  · exact Or.inr (Kq.suffix_vertex_eq j hj)

theorem reconnectedBackwardPath_vertex_eq (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (j : BipartiteVertex m n) (hj : D'.vertex j ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    j=.inl q.1.1 ∨ j=.inr p.1.2 := by
  rcases reconnectedBackwardPath_trace Kp Kq hm hj with (hj | hj) | hj
  · exact Or.inl (Kq.prefix_vertex_eq j hj)
  · exact False.elim (C.reconnection_segment_avoids_vertices p q hm D'.vertex hv false j hj)
  · exact Or.inr (Kp.suffix_vertex_eq j hj)

theorem reconnectedForwardPath_interior_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : BipartiteVertex m n) :
    reconnectedForwardPath Kp Kq hm t ≠ D'.vertex j :=
  path_interior_avoids_vertices_of_range D'.vertex _ _ _
    (reconnectedForwardPath_injective Kp Kq hm hemb)
    (reconnectedForwardPath_vertex_eq Kp Kq hm hv) t ht j

theorem reconnectedBackwardPath_interior_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : BipartiteVertex m n) :
    reconnectedBackwardPath Kp Kq hm t ≠ D'.vertex j :=
  path_interior_avoids_vertices_of_range D'.vertex _ _ _
    (reconnectedBackwardPath_injective Kp Kq hm hemb)
    (reconnectedBackwardPath_vertex_eq Kp Kq hm hv) t ht j

end Zarankiewicz

end

end OAI
