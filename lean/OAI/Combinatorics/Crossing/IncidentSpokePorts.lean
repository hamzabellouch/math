import OAI.Combinatorics.Crossing.DrawingSpokePorts
import OAI.Combinatorics.Crossing.RowCrossingCount

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def IncidentEdges (j : BipartiteVertex m n) :=
  {e : BipartiteEdge m n // j=Sum.inl e.1 ∨ j=Sum.inr e.2}

instance incidentEdgesFintype (j : BipartiteVertex m n) : Fintype (IncidentEdges j) := by
  classical
  unfold IncidentEdges
  infer_instance

theorem incident_edges_adjacent (j : BipartiteVertex m n) (e f : IncidentEdges j) :
    e.val.1=f.val.1 ∨ e.val.2=f.val.2 := by
  rcases e.property with he | he <;> rcases f.property with hf | hf
  · exact Or.inl (Sum.inl.inj (he.symm.trans hf))
  · cases he.symm.trans hf
  · cases he.symm.trans hf
  · exact Or.inr (Sum.inr.inj (he.symm.trans hf))

def drawingSpokePort (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (r : ℝ) (j : BipartiteVertex m n) (e : IncidentEdges j) : Plane :=
  if j=Sum.inl e.val.1 then (P e.val).startPort r else (P e.val).endPort r

theorem drawingSpokePort_interior (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (j : BipartiteVertex m n) (e : IncidentEdges j) :
    drawingSpokePort D P r j e ∈ edgeInterior D e.val := by
  unfold drawingSpokePort
  split_ifs
  · exact drawing_chain_startPort_interior D e.val (P e.val) (hmin e.val) r hr (hshort e.val).1
  · exact drawing_chain_endPort_interior D e.val (P e.val) (hmin e.val) r hr (hshort e.val).2

theorem drawingSpokePort_circle (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (j : BipartiteVertex m n) (e : IncidentEdges j) :
    squaredLength (drawingSpokePort D P r j e-D.vertex j)=r^2 := by
  unfold drawingSpokePort
  split_ifs with h
  · simpa only [h] using drawing_chain_startPort_circle D e.val (P e.val) (hmin e.val) r
  · have he := e.property.resolve_left h
    simpa only [he] using drawing_chain_endPort_circle D e.val (P e.val) (hmin e.val) r

theorem drawingSpokePort_injective (D : AdmissibleDrawing m n) (hnorm : NoAdjacentCrossings D)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r)
    (hshort : ∀ e, r^2 < squaredLength ((P e).vertices 1-(P e).vertices 0) ∧
      r^2 < squaredLength ((P e).vertices (P e).pieces-(P e).vertices ((P e).pieces-1)))
    (j : BipartiteVertex m n) : Function.Injective (drawingSpokePort D.toContinuousDrawing P r j) := by
  intro e f heq
  by_contra hne
  have hef : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  have hp := drawingSpokePort_interior D.toContinuousDrawing P hmin r hr hshort j e
  have hq := drawingSpokePort_interior D.toContinuousDrawing P hmin r hr hshort j f
  rw [← heq] at hq
  have hh : drawingSpokePort D.toContinuousDrawing P r j e ∈
      edgeInterior D.toContinuousDrawing e.val ∩ edgeInterior D.toContinuousDrawing f.val := ⟨hp,hq⟩
  rw [hnorm e.val f.val hef (incident_edges_adjacent j e f)] at hh
  exact hh

end Zarankiewicz

end

end OAI
