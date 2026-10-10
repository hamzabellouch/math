import OAI.Combinatorics.Crossing.OrderedPathParts
import OAI.Combinatorics.Crossing.AssembledPortIncidence
import OAI.Combinatorics.Crossing.ExtraDrawingSubdivision
import OAI.Combinatorics.Crossing.DrawingEdgeWalk

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem middlePath_contains_chord (E : PolygonalExterior C) (p : C.InnerIndex) :
    OrderedPathPart (E.middlePath p.1) (C.crossingChord p) := by
  rcases p with ⟨e,⟨i,hi⟩⟩
  have hj : i.val-1+1 < C.count e := by omega
  have hinner : C.orderedInner e (i.val-1) hj=⟨e,⟨i,hi⟩⟩ := by
    unfold DrawingPassages.orderedInner
    congr 1
    apply Subtype.ext
    apply Fin.ext
    change i.val-1+1=i.val
    omega
  have hpart : OrderedPathPart (E.middlePath e) (orderedBridge C e (i.val-1)) :=
    alternatingPath_contains_bridge _ _ _ _ (C.count e-1) (i.val-1) (by omega)
  apply hpart.congr_right
  intro t
  rw [orderedBridge_apply (C:=C) e (i.val-1) hj t,hinner]

theorem assembledEdge_contains_chord (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (p : C.InnerIndex) :
    OrderedPathPart (E.assembledEdge v p.1) (C.crossingChord p) := by
  have h : OrderedPathPart (E.anchoredMiddle p.1) (C.crossingChord p) := E.middlePath_contains_chord p
  exact (h.right (startSpoke C v p.1)).left (endSpoke C v p.1)

theorem assembled_crossing_ports_ordered (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (p : C.InnerIndex) :
    ∃ u w : unitInterval, u < w ∧
      E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p) ∧
      E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p) :=
  (E.assembledEdge_contains_chord v p).endpoints_ordered

theorem crossing_port_walk_indices (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p : C.InnerIndex) :
    ∃ i j : Fin ((P p.1).pieces+1), i < j ∧
      (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p) ∧
      (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p) := by
  obtain ⟨u,w,huw,hu,hw⟩ := E.assembled_crossing_ports_ordered v p
  obtain ⟨i,hi⟩ := hport p.1 u ⟨C.incomingPort p,hu.symm⟩
  obtain ⟨j,hj⟩ := hport p.1 w ⟨C.outgoingPort p,hw.symm⟩
  have hij : i < j := by
    by_contra hn
    have hh := (P p.1).increasing.monotone (le_of_not_gt hn)
    rw [hi,hj] at hh
    exact huw.not_ge hh
  refine ⟨i,j,hij,?_,?_⟩
  · rw [drawingEdgeWalk_getVert P p.1 i.val (by omega)]
    have he := (P p.1).vertices_at i
    change (P p.1).vertices i.val=E.assembledEdge v p.1 ((P p.1).knot i) at he
    exact he.trans ((congrArg (E.assembledEdge v p.1) hi).trans hu)
  · rw [drawingEdgeWalk_getVert P p.1 j.val (by omega)]
    have he := (P p.1).vertices_at j
    change (P p.1).vertices j.val=E.assembledEdge v p.1 ((P p.1).knot j) at he
    exact he.trans ((congrArg (E.assembledEdge v p.1) hj).trans hw)

end Zarankiewicz.PolygonalExterior

end

end OAI
