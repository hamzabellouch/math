import OAI.Combinatorics.CompleteCrossing.AdjacentSurgery

namespace OAI

/-! Surgery intersection containment, strict crossing reduction, and admissibility. -/

section

/-! Actual new chords cannot meet any third normalized edge, including at ports. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem segment_disjoint_of_open_containment (a b : Plane) (U S : Set Plane)
    (hin : openSegmentTrace a b ⊆ U) (hout : Disjoint S U)
    (ha : a ∉ S) (hb : b ∉ S) : Disjoint (segment ℝ a b) S := by
  apply Set.disjoint_left.mpr
  intro x hx hs
  rcases segment_endpoint_or_open a b x hx with rfl | rfl | hx
  · exact ha hs
  · exact hb hs
  · exact Set.disjoint_left.mp hout hs (hin hx)

namespace PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_port_not_mem_other_edge (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (r : C.Port) (her : e ≠ r.1.1) :
    C.portPoint r ∉ Set.range (E.assembledEdge v e) :=
  fun hx => her (E.assembled_port_unique_edge v hv e r hx)

theorem reconnection_other_edge_disjoint (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (i : Bool) (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    Disjoint (segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i))
      (Set.range (E.assembledEdge v e)) := by
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _
    (C.reconnection_open_in_disk p q hm i)
    (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
  · cases i
    · exact E.assembled_port_not_mem_other_edge v hv e (C.incomingPort q) heq
    · exact E.assembled_port_not_mem_other_edge v hv e (C.incomingPort p) hep
  · cases i
    · exact E.assembled_port_not_mem_other_edge v hv e (C.outgoingPort p) hep
    · exact E.assembled_port_not_mem_other_edge v hv e (C.outgoingPort q) heq

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Each new chord avoids the retained cuts assigned to the other switched walk. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Exact retained-track cases for intersections of the two actual rerouted paths. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Every contact of rerouted edges is carried by the original drawing tracks. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem reconnectedForwardPath_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1)
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
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases reconnectedBackwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · exact Or.inr (Kq.prefix_subset_edge hx)
  · exact False.elim (Set.disjoint_left.mp (E.reconnection_other_edge_disjoint v hv p q hpq hm false e hep heq) hx hy)
  · exact Or.inl (Kp.suffix_subset_edge hx)

theorem adjacentSurgeryRoutes_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1)
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
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
    (hy : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∧ x ∈ Set.range (E.assembledEdge v q.1) := by
  have hh := E.reconnected_paths_meeting_old_edges v hvinj hv hdet P Kp Kq hpq hm hcross x
  by_cases h : (graph.src p.1)=(graph.src q.1)
  · simp only [adjacentSurgeryRouteP,adjacentSurgeryRouteQ,dite_eq_left h] at hx hy
    exact hh hy hx
  · simp only [adjacentSurgeryRouteP,adjacentSurgeryRouteQ,dite_eq_right h] at hx hy
    exact hh hx hy

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Every actual spatial crossing of the surgery drawing was already a crossing before surgery. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem adjacentSurgeryDrawing_crossings_subset
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) ⊆
      Paper170.crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing := by
  let B := (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  intro x hx
  obtain ⟨e,f,hef,hxe,hxf⟩ := hx
  have havoid : ∀ j, x ≠ B.vertex j := edgeInterior_not_vertex A e x hxe
  have hpair (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
      (hy : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj)) : x ∈ Paper170.crossingPoints B := by
    have hh := E.adjacentSurgeryRoutes_meeting_each_other v hvinj hv hdet P Kp Kq hpq hm hadj hcross x hx hy
    exact crossing_of_ranges_not_vertices B p.1 q.1
      (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) x hh.1 hh.2 havoid
  have hmixed (g : Edge) (hgp : g ≠ p.1) (hgq : g ≠ q.1)
      (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
        x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (hy : x ∈ Set.range (B.edge g)) : x ∈ Paper170.crossingPoints B := by
    rcases E.adjacentSurgeryRoutes_meeting_other v hvinj hv hdet P Kp Kq hpq hm hadj g hgp hgq x hx hy with h | h
    · exact crossing_of_ranges_not_vertices B p.1 g (Ne.symm hgp) x h hy havoid
    · exact crossing_of_ranges_not_vertices B q.1 g (Ne.symm hgq) x h hy havoid
  have hcases (g : Edge) (hg : x ∈ Set.range (A.edge g)) :=
    B.replaceTwoRoutes_range_cases p.1 q.1 (adjacentSurgeryRouteP Kp Kq hm hadj)
      (adjacentSurgeryRouteQ Kp Kq hm hadj) g x hg
  rcases hcases e (edgeInterior_subset_range A e hxe) with ⟨hep,hx⟩ | ⟨heq,hx⟩ | ⟨hep,heq,hx⟩
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact False.elim (hef (hep.trans hfp.symm))
    · exact hpair hx hy
    · exact hmixed f hfp hfq (Or.inl hx) hy
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hpair hy hx
    · exact False.elim (hef (heq.trans hfq.symm))
    · exact hmixed f hfp hfq (Or.inr hx) hy
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hmixed e hep heq (Or.inl hy) hx
    · exact hmixed e hep heq (Or.inr hy) hx
    · exact crossing_of_ranges_not_vertices B e f hef x hx hy havoid

end Paper170Geometry.PolygonalExterior

end
end

section

/-! A strict decrease of the actual spatial crossing set; properness of the new drawing is still separate. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  {p q : C.InnerIndex}

theorem crossingChord_meeting_is_assembled_crossing (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ Paper170.crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hxin := (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1
  have hxinq : x ∈ C.crossingDisk q := by
    simpa only [DrawingPassages.crossingDisk,hm] using hxin
  apply crossing_of_ranges_not_vertices (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing
    p.1 q.1 (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) x
    ((E.assembled_range_in_crossingDisk v hv p x hxin).mpr hxp)
    ((E.assembled_range_in_crossingDisk v hv q x hxinq).mpr hxq)
  intro j he
  exact Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p j) hxin (he.symm ▸ (hv j).le)

theorem adjacentSurgeryDrawing_strict_crossing_ncard
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    (Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb)).Finite ∧
      (Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb)).ncard <
        (Paper170.crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing).ncard := by
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  have hsub := E.adjacentSurgeryDrawing_crossings_subset v hvinj hv hdet P Kp Kq hpq hm hadj hcross hemb
  have hfinite := (E.assembledAdmissible v hvinj hv hdet).crossings_finite
  have hremoved := adjacentSurgeryDrawing_avoids_crossing Kp Kq hm hpq hadj hv hemb x hxp hxq (by
    intro e hep heq hx
    exact Set.disjoint_left.mp (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
      hx (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1)
  have hnot : x ∉ Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) := by
    rintro ⟨e,f,hef,hxe,hxf⟩
    exact hremoved e (edgeInterior_subset_range _ e hxe)
  refine ⟨hfinite.subset hsub,Set.ncard_lt_ncard ⟨hsub,?_⟩ hfinite⟩
  intro hrev
  exact hnot (hrev (E.crossingChord_meeting_is_assembled_crossing v hvinj hv hdet hpq x hxp hxq))

end Paper170Geometry.PolygonalExterior

end
end

section

/-! The actual surgery drawing has no triple interior contacts. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

theorem adjacentSurgeryDrawing_no_triples
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e f g : Edge) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    Paper170.edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) e ∩
      Paper170.edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) f ∩
      Paper170.edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) g = ∅ := by
  let B := E.assembledAdmissible v hvinj hv hdet
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨⟨hxe,hxf⟩,hxg⟩ := hx
  have havoid : ∀ j, x ≠ B.vertex j := edgeInterior_not_vertex A e x hxe
  have hthree (a b c : Edge) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (ha : x ∈ Set.range (B.edge a)) (hb : x ∈ Set.range (B.edge b))
      (hc : x ∈ Set.range (B.edge c)) : False := by
    have hmem : x ∈ Paper170.edgeInterior B.toContinuousDrawing a ∩ Paper170.edgeInterior B.toContinuousDrawing b ∩
        Paper170.edgeInterior B.toContinuousDrawing c :=
      ⟨⟨edgeInterior_of_range_not_vertices _ a x ha havoid,
        edgeInterior_of_range_not_vertices _ b x hb havoid⟩,edgeInterior_of_range_not_vertices _ c x hc havoid⟩
    rw [B.no_triples a b c hab hac hbc] at hmem
    exact hmem
  have htwo (a : Edge) (hap : a ≠ p.1) (haq : a ≠ q.1)
      (hp : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
      (hq : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (ha : x ∈ Set.range (B.edge a)) : False := by
    have hh := E.adjacentSurgeryRoutes_meeting_each_other v hvinj hv hdet P Kp Kq hpq hm hadj hcross x hp hq
    exact hthree p.1 q.1 a (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm))
      (Ne.symm hap) (Ne.symm haq) hh.1 hh.2 ha
  have hone (a b : Edge) (hab : a ≠ b)
      (hap : a ≠ p.1) (haq : a ≠ q.1) (hbp : b ≠ p.1) (hbq : b ≠ q.1)
      (hh : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
        x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (ha : x ∈ Set.range (B.edge a)) (hb : x ∈ Set.range (B.edge b)) : False := by
    rcases E.adjacentSurgeryRoutes_meeting_other v hvinj hv hdet P Kp Kq hpq hm hadj a hap haq x hh ha with hp | hq
    · exact hthree p.1 a b (Ne.symm hap) (Ne.symm hbp) hab hp ha hb
    · exact hthree q.1 a b (Ne.symm haq) (Ne.symm hbq) hab hq ha hb
  have hcases (a : Edge) (ha : x ∈ Set.range (A.edge a)) :=
    B.toContinuousDrawing.replaceTwoRoutes_range_cases p.1 q.1 (adjacentSurgeryRouteP Kp Kq hm hadj)
      (adjacentSurgeryRouteQ Kp Kq hm hadj) a x ha
  have hec := hcases e (edgeInterior_subset_range A e hxe)
  have hfc := hcases f (edgeInterior_subset_range A f hxf)
  have hgc := hcases g (edgeInterior_subset_range A g hxg)
  rcases hec with ⟨hep,hx⟩ | ⟨heq,hx⟩ | ⟨hep,heq,hx⟩
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hef (hep.trans hfp.symm)
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact heg (hep.trans hgp.symm)
      · exact hfg (hfq.trans hgq.symm)
      · exact htwo g hgp hgq hx hy hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact heg (hep.trans hgp.symm)
      · exact htwo f hfp hfq hx hz hy
      · exact hone f g hfg hfp hfq hgp hgq (Or.inl hx) hy hz
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hfg (hfp.trans hgp.symm)
      · exact heg (heq.trans hgq.symm)
      · exact htwo g hgp hgq hy hx hz
    · exact hef (heq.trans hfq.symm)
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact htwo f hfp hfq hz hx hy
      · exact heg (heq.trans hgq.symm)
      · exact hone f g hfg hfp hfq hgp hgq (Or.inr hx) hy hz
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hfg (hfp.trans hgp.symm)
      · exact htwo e hep heq hy hz hx
      · exact hone e g heg hep heq hgp hgq (Or.inl hy) hx hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact htwo e hep heq hz hy hx
      · exact hfg (hfq.trans hgq.symm)
      · exact hone e g heg hep heq hgp hgq (Or.inr hy) hx hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hone e f hef hep heq hfp hfq (Or.inl hz) hx hy
      · exact hone e f hef hep heq hfp hfq (Or.inr hz) hx hy
      · exact hthree e f g hef heg hfg hx hy hz

end Paper170Geometry.PolygonalExterior

end
end

section

/-! The constructed surgery drawing satisfies exactly the proved weaker normalization input. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}

def adjacentSurgeryFiniteDrawing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    FiniteIntersectionDrawing graph where
  toContinuousDrawing := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  crossings_finite := (E.adjacentSurgeryDrawing_strict_crossing_ncard v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq).1
  no_triples := E.adjacentSurgeryDrawing_no_triples v hvinj hv hdet P Kp Kq hpq hm hadj
    (C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq) hemb

theorem adjacentSurgeryFiniteDrawing_count_lt
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    finiteCrossingCount (E.adjacentSurgeryFiniteDrawing v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq) <
      Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) := by
  rw [finiteCrossingCount_eq_ncard]
  have h := (E.adjacentSurgeryDrawing_strict_crossing_ncard v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq).2
  exact h.trans_eq (Set.ncard_eq_toFinset_card _ (E.assembledAdmissible v hvinj hv hdet).crossings_finite)

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Strict adjacent-crossing improvement with actual admissibility restored by proved normalization. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem exists_admissible_adjacent_surgery [Fintype Vertex] [Fintype Edge] (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    ∃ A : Paper170.AdmissibleDrawing graph, (∀ e, HasFiniteAffineCover (A.edge e)) ∧
      Paper170.crossingCount A < Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  obtain ⟨P,hmark,hport⟩ := E.exists_assembled_port_subdivision v hvinj hv hdet
  obtain ⟨Kp⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport p
  obtain ⟨Kq⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport q
  have hemb := crossingSurgeryGraph_embedding C P hmark hport p q hm hcross
  let B := E.adjacentSurgeryFiniteDrawing v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq
  obtain ⟨A,hpoly,hcount⟩ := finite_intersection_normalization B
  exact ⟨A,hpoly,hcount.trans_lt
    (E.adjacentSurgeryFiniteDrawing_count_lt v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq)⟩

end Paper170Geometry.PolygonalExterior

end
end

end OAI
