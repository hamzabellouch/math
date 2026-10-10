import OAI.Combinatorics.Crossing.ReconnectionOtherEdges
import OAI.Combinatorics.Crossing.CutTraceSeparation

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalExterior
variable {m n : ℕ} {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem forward_chord_disjoint_opposite_prefix
    (Kq : ExteriorCrossingCut C P q) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val))) := by
  have hqp : q.1 ≠ p.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he.symm hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _ (C.reconnection_open_in_disk p q hm true)
  · simpa only [DrawingPassages.crossingDisk,hm] using Kq.prefix_outside
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv q.1 (C.incomingPort p) hqp (Kq.prefix_subset_edge hx)
  · exact Kq.outgoing_not_prefix

theorem forward_chord_disjoint_opposite_suffix
    (Kp : ExteriorCrossingCut C P p) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val))) := by
  have hpqe : p.1 ≠ q.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _
    (C.reconnection_open_in_disk p q hm true) Kp.suffix_outside
  · exact Kp.incoming_not_suffix
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv p.1 (C.outgoingPort q) hpqe (Kp.suffix_subset_edge hx)

theorem backward_chord_disjoint_opposite_prefix
    (Kp : ExteriorCrossingCut C P p) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val))) := by
  have hpqe : p.1 ≠ q.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _
    (C.reconnection_open_in_disk p q hm false) Kp.prefix_outside
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv p.1 (C.incomingPort q) hpqe (Kp.prefix_subset_edge hx)
  · exact Kp.outgoing_not_prefix

theorem backward_chord_disjoint_opposite_suffix
    (Kq : ExteriorCrossingCut C P q) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val))) := by
  have hqp : q.1 ≠ p.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he.symm hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _ (C.reconnection_open_in_disk p q hm false)
  · simpa only [DrawingPassages.crossingDisk,hm] using Kq.suffix_outside
  · exact Kq.incoming_not_suffix
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv q.1 (C.outgoingPort p) hqp (Kq.suffix_subset_edge hx)

end Zarankiewicz.PolygonalExterior

end

end OAI
