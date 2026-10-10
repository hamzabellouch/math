import OAI.Combinatorics.Crossing.CrossingPortClearance
import OAI.Combinatorics.Crossing.DrawingWalkCutTraces
import OAI.Combinatorics.Crossing.ExteriorSegmentGraph

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem crossing_cut_traces_disjoint (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (p : C.InnerIndex) (i j : Fin ((P p.1).pieces+1))
    (hi : (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p))
    (hj : (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p)) :
    Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take i.val))) (C.crossingDisk p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop j.val))) (C.crossingDisk p) := by
  have hki : (drawingEdgeWalk P p.1).getVert i.val=E.assembledEdge v p.1 ((P p.1).knot i) :=
    (drawingEdgeWalk_getVert P p.1 i.val (by omega)).trans ((P p.1).vertices_at i)
  have hkj : (drawingEdgeWalk P p.1).getVert j.val=E.assembledEdge v p.1 ((P p.1).knot j) :=
    (drawingEdgeWalk_getVert P p.1 j.val (by omega)).trans ((P p.1).vertices_at j)
  have hu := hki.symm.trans hi
  have hw := hkj.symm.trans hj
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx hxin
    obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P p.1 i hx
    exact E.assembled_crossing_port_clearance v hv p _ _ hu hw t (Or.inl ht.2) (he.symm ▸ hxin)
  · apply Set.disjoint_left.mpr
    intro x hx hxin
    obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P p.1 j hx
    exact E.assembled_crossing_port_clearance v hv p _ _ hu hw t (Or.inr ht.1) (he.symm ▸ hxin)

theorem exists_exterior_crossing_cuts (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p : C.InnerIndex) :
    ∃ i j : Fin ((P p.1).pieces+1), i < j ∧
      (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p) ∧
      (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take i.val))) (C.crossingDisk p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop j.val))) (C.crossingDisk p) := by
  obtain ⟨i,j,hij,hi,hj⟩ := E.crossing_port_walk_indices v hvinj hv hdet P hport p
  exact ⟨i,j,hij,hi,hj,E.crossing_cut_traces_disjoint v hvinj hv hdet P p i j hi hj⟩

end Zarankiewicz.PolygonalExterior

end

end OAI
