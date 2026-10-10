import OAI.Combinatorics.Crossing.DrawingSubdivisionGraph
import OAI.Combinatorics.Crossing.GraphSequenceWalk

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : AdmissibleDrawing m n}

theorem drawingEdgeSequence_adj (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : BipartiteEdge m n) (i : ℕ) (hi : i < (P e).pieces) :
    (drawingSubdivisionGraph P).Adj ((P e).vertices i) ((P e).vertices (i+1)) := by
  let j : Fin (P e).pieces := ⟨i,hi⟩
  have h0 : (P e).vertices i=drawingPieceStart P ⟨e,j⟩ := (P e).vertices_at j.castSucc
  have h1 : (P e).vertices (i+1)=drawingPieceEnd P ⟨e,j⟩ := (P e).vertices_at j.succ
  rw [h0,h1]
  exact drawingSubdivisionGraph_piece_adj P ⟨e,j⟩

def drawingEdgeWalk (P : ∀ e, PolygonalParametrization (D.edge e)) (e : BipartiteEdge m n) :
    (drawingSubdivisionGraph P).Walk (D.vertex (.inl e.1)) (D.vertex (.inr e.2)) :=
  (graphSequenceWalk (drawingSubdivisionGraph P) (P e).vertices (P e).pieces
    (drawingEdgeSequence_adj P e)).copy (P e).vertices_first (P e).vertices_last

theorem drawingEdgeWalk_length (P : ∀ e, PolygonalParametrization (D.edge e)) (e : BipartiteEdge m n) :
    (drawingEdgeWalk P e).length=(P e).pieces := by
  simp only [drawingEdgeWalk,SimpleGraph.Walk.length_copy,graphSequenceWalk_length]

theorem drawingEdgeWalk_getVert (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : BipartiteEdge m n) (i : ℕ) (hi : i ≤ (P e).pieces) :
    (drawingEdgeWalk P e).getVert i=(P e).vertices i := by
  simp only [drawingEdgeWalk,SimpleGraph.Walk.getVert_copy]
  exact graphSequenceWalk_getVert _ _ _ _ i hi

theorem drawingEdgeWalk_isPath (P : ∀ e, PolygonalParametrization (D.edge e)) (e : BipartiteEdge m n) :
    (drawingEdgeWalk P e).IsPath := by
  rw [drawingEdgeWalk,SimpleGraph.Walk.isPath_copy]
  apply graphSequenceWalk_isPath
  intro i hi j hj he
  change i ≤ (P e).pieces at hi
  change j ≤ (P e).pieces at hj
  have h0 := (P e).vertices_at (⟨i,by omega⟩ : Fin ((P e).pieces+1))
  have h1 := (P e).vertices_at (⟨j,by omega⟩ : Fin ((P e).pieces+1))
  rw [h0,h1] at he
  have hh := (P e).increasing.injective (D.edge_injective e he)
  exact congrArg Fin.val hh

theorem drawingEdgeWalk_uniqueVisit (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : BipartiteEdge m n) (x : Plane) : UniqueWalkVisit (drawingEdgeWalk P e) x := by
  intro i j hi hj hix hjx
  exact (drawingEdgeWalk_isPath P e).getVert_injOn hi hj (hix.trans hjx.symm)

end Zarankiewicz

end

end OAI
