import OAI.Combinatorics.Crossing.ReconnectedIntersectionCases

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

theorem reconnectedForwardPath_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (reconnectedForwardPath Kp Kq hm))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases reconnectedForwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · exact Or.inl (Kp.prefix_subset_edge hx)
  · exact False.elim (Set.disjoint_left.mp (E.reconnection_other_edge_disjoint v hv p q hpq hm true e hep heq) hx hy)
  · exact Or.inr (Kq.suffix_subset_edge hx)

theorem reconnectedBackwardPath_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases reconnectedBackwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · exact Or.inr (Kq.prefix_subset_edge hx)
  · exact False.elim (Set.disjoint_left.mp (E.reconnection_other_edge_disjoint v hv p q hpq hm false e hep heq) hx hy)
  · exact Or.inl (Kp.suffix_subset_edge hx)

theorem adjacentSurgeryRoutes_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
      x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  have hf := E.reconnectedForwardPath_meeting_other v hvinj hv hdet P Kp Kq hpq hm e hep heq x
  have hb := E.reconnectedBackwardPath_meeting_other v hvinj hv hdet P Kp Kq hpq hm e hep heq x
  rcases hx with hx | hx
  · unfold adjacentSurgeryRouteP at hx
    split at hx
    · exact hb hx hy
    · exact hf hx hy
  · unfold adjacentSurgeryRouteQ at hx
    split at hx
    · exact hf hx hy
    · exact hb hx hy

theorem adjacentSurgeryRoutes_meeting_each_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
    (hy : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∧ x ∈ Set.range (E.assembledEdge v q.1) := by
  have hh := E.reconnected_paths_meeting_old_edges v hvinj hv hdet P Kp Kq hpq hm hcross x
  by_cases h : p.1.1=q.1.1
  · simp only [adjacentSurgeryRouteP,adjacentSurgeryRouteQ,dite_eq_left h] at hx hy
    exact hh hy hx
  · simp only [adjacentSurgeryRouteP,adjacentSurgeryRouteQ,dite_eq_right h] at hx hy
    exact hh hx hy

end Zarankiewicz.PolygonalExterior

end

end OAI
