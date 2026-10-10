import OAI.Combinatorics.Crossing.ReconnectionOppositeCuts

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

theorem reconnected_paths_meeting_cases
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (reconnectedForwardPath Kp Kq hm))
    (hy : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    (x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∧
      x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val))) ∨
    (x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) ∧
      x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val))) := by
  have hFP := E.forward_chord_disjoint_opposite_prefix v hvinj hv hdet P Kq hpq hm
  have hFS := E.forward_chord_disjoint_opposite_suffix v hvinj hv hdet P Kp hpq hm
  have hBP := E.backward_chord_disjoint_opposite_prefix v hvinj hv hdet P Kp hpq hm
  have hBS := E.backward_chord_disjoint_opposite_suffix v hvinj hv hdet P Kq hpq hm
  have hchord := C.reconnection_chords_disjoint p q hcross true false (by decide)
  rcases reconnectedForwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · rcases reconnectedBackwardPath_trace Kp Kq hm hy with (hy | hy) | hy
    · exact Or.inl ⟨hx,hy⟩
    · exact False.elim (Set.disjoint_left.mp hBP hy hx)
    · exact False.elim (Set.disjoint_left.mp Kp.prefix_suffix_disjoint hx hy)
  · rcases reconnectedBackwardPath_trace Kp Kq hm hy with (hy | hy) | hy
    · exact False.elim (Set.disjoint_left.mp hFP hx hy)
    · exact False.elim (Set.disjoint_left.mp hchord hx hy)
    · exact False.elim (Set.disjoint_left.mp hFS hx hy)
  · rcases reconnectedBackwardPath_trace Kp Kq hm hy with (hy | hy) | hy
    · exact False.elim (Set.disjoint_left.mp Kq.prefix_suffix_disjoint hy hx)
    · exact False.elim (Set.disjoint_left.mp hBS hy hx)
    · exact Or.inr ⟨hy,hx⟩

theorem reconnected_paths_meeting_old_edges
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (reconnectedForwardPath Kp Kq hm))
    (hy : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∧ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases E.reconnected_paths_meeting_cases v hvinj hv hdet P Kp Kq hpq hm hcross x hx hy with h | h
  · exact ⟨Kp.prefix_subset_edge h.1,Kq.prefix_subset_edge h.2⟩
  · exact ⟨Kp.suffix_subset_edge h.1,Kq.suffix_subset_edge h.2⟩

end Zarankiewicz.PolygonalExterior

end

end OAI
