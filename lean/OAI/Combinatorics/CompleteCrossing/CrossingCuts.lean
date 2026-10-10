import OAI.Combinatorics.CompleteCrossing.Reconnection
import OAI.Combinatorics.Crossing.ExteriorSegmentGraph
import OAI.Combinatorics.Crossing.GraphWalkRealizationLaws
import OAI.Combinatorics.Crossing.OrderedPathParts
import OAI.Combinatorics.Crossing.SegmentAugmentation

namespace OAI

/-! Ordered crossing ports, surgery cut walks, path witnesses, and cut separation. -/

section

/-! The actual embedded surgery graph: exterior drawing tracks and two disjoint reconnection chords. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}

def crossingSurgeryGraph (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) : SimpleGraph Plane :=
  segmentAugmentedGraph (exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p))
    (C.reconnectionStart p q) (C.reconnectionEnd p q) (C.reconnection_endpoints_ne p q)

theorem crossingSurgeryGraph_embedding (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e))
    (hmark : ∀ e t, D'.edge e t ∈ drawingMarks D'.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (hport : ∀ e t, D'.edge e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p q : C.InnerIndex) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) :
    StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id := by
  have hemb := drawingSubdivisionGraph_embedding P hmark
  have houtEmb : StraightEdgeEmbedding
      (exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p)) id := by
    refine ⟨hemb.1,?_⟩
    intro a b c d hab hcd x hx hy
    exact hemb.2 a b c d hab.1 hcd.1 x hx hy
  apply segmentAugmentedGraph_embedding _ _ _ _ houtEmb (C.crossingDisk p)
  · intro x y hxy
    exact hxy.2
  · exact C.reconnection_open_in_disk p q hm
  · exact C.reconnection_chords_disjoint p q hcross
  · intro i x y hxy
    constructor
    · apply drawingSubdivisionGraph_point_endpoint P _ ?_ x y hxy.1
      intro e t ht
      apply hport e t
      cases i
      · exact ⟨C.incomingPort q,ht.symm⟩
      · exact ⟨C.incomingPort p,ht.symm⟩
    · apply drawingSubdivisionGraph_point_endpoint P _ ?_ x y hxy.1
      intro e t ht
      apply hport e t
      cases i
      · exact ⟨C.outgoingPort p,ht.symm⟩
      · exact ⟨C.outgoingPort q,ht.symm⟩

theorem exterior_le_crossingSurgeryGraph (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) :
    exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p) ≤ crossingSurgeryGraph C P p q :=
  le_segmentAugmentedGraph _ _ _ _

theorem crossingSurgeryGraph_reconnection_adj (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) (i : Bool) :
    (crossingSurgeryGraph C P p q).Adj (C.reconnectionStart p q i) (C.reconnectionEnd p q i) :=
  segmentAugmentedGraph_added_adj _ _ _ _ i

end Paper170Geometry

end
end

section

/-! The actual incoming and outgoing ports occur in the correct order on each edge. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

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
    (v : Vertex → Plane) (p : C.InnerIndex) :
    OrderedPathPart (E.assembledEdge v p.1) (C.crossingChord p) := by
  have h : OrderedPathPart (E.anchoredMiddle p.1) (C.crossingChord p) := E.middlePath_contains_chord p
  exact (h.right (startSpoke C v p.1)).left (endSpoke C v p.1)

theorem assembled_crossing_ports_ordered (E : PolygonalExterior C)
    (v : Vertex → Plane) (p : C.InnerIndex) :
    ∃ u w : unitInterval, u < w ∧
      E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p) ∧
      E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p) :=
  (E.assembledEdge_contains_chord v p).endpoints_ordered

theorem crossing_port_walk_indices (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Exactly the two incident assembled edges can enter a chosen crossing disk. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_in_crossingDisk_chord (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (p : C.InnerIndex) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hxin : x ∈ C.crossingDisk p) :
    ∃ r : C.InnerIndex, r.1=e ∧ C.innerMark r=C.innerMark p ∧ x ∈ Set.range (C.crossingChord r) := by
  rcases (E.assembledEdge_range_iff v e x).mp hx with (hx | ⟨i,hi,hx⟩ | ⟨r,hr,hx⟩) | hx
  · exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
      hxin (C.vertex_spoke_range_in_disk v hv _ (C.startPortAt e) hx))
  · obtain ⟨t,rfl⟩ := hx
    exact False.elim (hxin.not_ge (E.outside_open_disks i t (C.innerMark p)))
  · refine ⟨r,hr,?_,hx⟩
    by_contra hn
    exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
      (C.crossingChord_range_subset_disk r hx) (C.crossingDisk_subset_closed p hxin)
  · rw [endSpoke_range] at hx
    exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
      hxin (C.vertex_spoke_range_in_disk v hv _ (C.endPortAt e) hx))

theorem assembled_crossingDisk_owner (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : Edge) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hxin : x ∈ C.crossingDisk p) : e=p.1 ∨ e=q.1 := by
  obtain ⟨r,hr,hrm,hxr⟩ := E.assembled_in_crossingDisk_chord v hv e p x hx hxin
  rcases C.innerIndex_at_mark_pair p q r hpq hm hrm.symm with rfl | rfl
  · exact Or.inl hr.symm
  · exact Or.inr hr.symm

theorem assembled_other_edge_avoids_crossingDisk (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    Disjoint (Set.range (E.assembledEdge v e)) (C.crossingDisk p) := by
  apply Set.disjoint_left.mpr
  intro x hx hxin
  rcases E.assembled_crossingDisk_owner v hv p q hpq hm e x hx hxin with h | h
  · exact hep h
  · exact heq h

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Before the incoming port and after the outgoing port, the actual edge avoids the open crossing disk. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : Paper170.AdmissibleDrawing graph}

theorem crossingChord_parameter_interior (C : DrawingPassages D.toFiniteIntersectionDrawing) (p : C.InnerIndex)
    (t : unitInterval) (ht : C.crossingChord p t ∈ C.crossingDisk p) :
    t ∈ Set.Ioo (0 : unitInterval) 1 := by
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    change squaredLength (C.crossingChord p 0-(C.innerMark p).val) < C.radius^2 at ht
    rw [Path.source,C.incomingPoint_on_circle] at ht
    exact lt_irrefl _ ht
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    change squaredLength (C.crossingChord p 1-(C.innerMark p).val) < C.radius^2 at ht
    rw [Path.target,C.outgoingPoint_on_circle] at ht
    exact lt_irrefl _ ht
  exact ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩

end DrawingPassages
namespace PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem assembled_crossing_disk_parameter_between (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (u w : unitInterval)
    (hu : E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p))
    (hw : E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p))
    (t : unitInterval) (ht : E.assembledEdge v p.1 t ∈ C.crossingDisk p) : u < t ∧ t < w := by
  obtain ⟨f,hf,he⟩ := E.assembledEdge_contains_chord v p
  have h0 : f 0=u := E.assembledEdge_injective v hv p.1
    (((he 0).trans (C.crossingChord p).source).trans hu.symm)
  have h1 : f 1=w := E.assembledEdge_injective v hv p.1
    (((he 1).trans (C.crossingChord p).target).trans hw.symm)
  have hmem : E.assembledEdge v p.1 t ∈ Set.range (C.crossingChord p) :=
    (E.assembled_range_in_crossingDisk v hv p _ ht).mp ⟨t,rfl⟩
  obtain ⟨s,hs⟩ := hmem
  have hsint := C.crossingChord_parameter_interior p s (hs.symm ▸ ht)
  have hst : f s=t := E.assembledEdge_injective v hv p.1 ((he s).trans hs)
  exact ⟨by simpa only [h0,hst] using hf hsint.1,by simpa only [h1,hst] using hf hsint.2⟩

theorem assembled_crossing_port_clearance (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (u w : unitInterval)
    (hu : E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p))
    (hw : E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p))
    (t : unitInterval) (ht : t ≤ u ∨ w ≤ t) : E.assembledEdge v p.1 t ∉ C.crossingDisk p := by
  intro hmem
  have hbetween := E.assembled_crossing_disk_parameter_between v hv p u w hu hw t hmem
  rcases ht with ht | ht
  · exact hbetween.1.not_ge ht
  · exact hbetween.2.not_ge ht

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Actual ordered prefix and suffix cuts lie in the exterior segment graph. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem crossing_cut_traces_disjoint (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
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
    (v : Vertex → Plane) (hvinj : Function.Injective v)
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

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Actual prefix and suffix walks transferred to the constructed surgery graph. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}

def surgeryPrefixWalk (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (i : ℕ) (hi : (drawingEdgeWalk P r.1).getVert i=C.portPoint (C.incomingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i))) (C.crossingDisk p)) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src r.1))) (C.portPoint (C.incomingPort r)) :=
  ((exteriorGraphWalk ((drawingEdgeWalk P r.1).take i) (C.crossingDisk p) hout).mapLe
    (exterior_le_crossingSurgeryGraph C P p q)).copy rfl hi

def surgerySuffixWalk (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (j : ℕ) (hj : (drawingEdgeWalk P r.1).getVert j=C.portPoint (C.outgoingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j))) (C.crossingDisk p)) :
    (crossingSurgeryGraph C P p q).Walk (C.portPoint (C.outgoingPort r)) (D'.vertex ((graph.dst r.1))) :=
  ((exteriorGraphWalk ((drawingEdgeWalk P r.1).drop j) (C.crossingDisk p) hout).mapLe
    (exterior_le_crossingSurgeryGraph C P p q)).copy hj rfl

theorem surgeryPrefixWalk_trace (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (i : ℕ) (hi : (drawingEdgeWalk P r.1).getVert i=C.portPoint (C.incomingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i))) (C.crossingDisk p)) :
    Set.range (graphWalkPath id (surgeryPrefixWalk C P p q r i hi hout))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i)) := by
  rw [surgeryPrefixWalk,graphWalkPath_copy_range,graphWalkPath_mapLe_range,exteriorGraphWalk_trace]

theorem surgerySuffixWalk_trace (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (j : ℕ) (hj : (drawingEdgeWalk P r.1).getVert j=C.portPoint (C.outgoingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j))) (C.crossingDisk p)) :
    Set.range (graphWalkPath id (surgerySuffixWalk C P p q r j hj hout))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j)) := by
  rw [surgerySuffixWalk,graphWalkPath_copy_range,graphWalkPath_mapLe_range,exteriorGraphWalk_trace]

end Paper170Geometry

end
end

section

/-! Ordered actual cut data, whose existence is proved for the constructed normalization. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}

structure ExteriorCrossingCut (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (r : C.InnerIndex) where
  first : Fin ((P r.1).pieces+1)
  last : Fin ((P r.1).pieces+1)
  ordered : first < last
  first_point : (drawingEdgeWalk P r.1).getVert first.val=C.portPoint (C.incomingPort r)
  last_point : (drawingEdgeWalk P r.1).getVert last.val=C.portPoint (C.outgoingPort r)
  prefix_outside : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take first.val))) (C.crossingDisk r)
  suffix_outside : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop last.val))) (C.crossingDisk r)

theorem PolygonalExterior.nonempty_exteriorCrossingCut {C : DrawingPassages D.toFiniteIntersectionDrawing} (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (r : C.InnerIndex) : Nonempty (ExteriorCrossingCut C P r) := by
  obtain ⟨i,j,hij,hi,hj,hout,hout'⟩ := E.exists_exterior_crossing_cuts v hvinj hv hdet P hport r
  exact ⟨⟨i,j,hij,hi,hj,hout,hout'⟩⟩

namespace ExteriorCrossingCut
variable {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q r : C.InnerIndex}

def prefixInSurgery (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src r.1))) (C.portPoint (C.incomingPort r)) :=
  surgeryPrefixWalk C P p q r K.first.val K.first_point (by
    simpa only [DrawingPassages.crossingDisk,hr] using K.prefix_outside)

def suffixInSurgery (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    (crossingSurgeryGraph C P p q).Walk (C.portPoint (C.outgoingPort r)) (D'.vertex ((graph.dst r.1))) :=
  surgerySuffixWalk C P p q r K.last.val K.last_point (by
    simpa only [DrawingPassages.crossingDisk,hr] using K.suffix_outside)

theorem prefixInSurgery_trace (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    Set.range (graphWalkPath id (K.prefixInSurgery p q hr))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) :=
  surgeryPrefixWalk_trace _ _ _ _ _ _ _ _

theorem suffixInSurgery_trace (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    Set.range (graphWalkPath id (K.suffixInSurgery p q hr))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) :=
  surgerySuffixWalk_trace _ _ _ _ _ _ _ _

end ExteriorCrossingCut
end Paper170Geometry

end
end

section

/-! Simple actual polygonal paths obtained from transferred tracks and one new chord. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

def walkThroughChord {G : SimpleGraph Plane} {a u v b : Plane}
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) : G.Walk a b :=
  (A.append h.toWalk).append B

theorem walkThroughChord_range {G : SimpleGraph Plane} {a u v b : Plane}
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) :
    Set.range (graphWalkPath id (walkThroughChord A h B))=
      (Set.range (graphWalkPath id A) ∪ segment ℝ u v) ∪ Set.range (graphWalkPath id B) := by
  rw [walkThroughChord,graphWalkPath_append_range,graphWalkPath_append_range,graphWalkPath_toWalk_range]

theorem exists_simple_path_through_chord {G : SimpleGraph Plane}
    (hemb : StraightEdgeEmbedding G id) {a u v b : Plane} (hab : a ≠ b)
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) :
    ∃ γ : Path a b, Function.Injective γ ∧ HasFiniteAffineCover γ ∧
      Set.range γ ⊆ (Set.range (graphWalkPath id A) ∪ segment ℝ u v) ∪ Set.range (graphWalkPath id B) := by
  classical
  let p := walkThroughChord A h B
  refine ⟨graphWalkPath id p.bypass,
    graphWalkPath_injective id hemb hab p.bypass p.bypass_isPath,
    graphWalkPath_hasFiniteAffineCover id p.bypass,?_⟩
  exact (graphWalkPath_bypass_range_subset id p).trans (by rw [walkThroughChord_range])

variable  {D D' : Paper170.AdmissibleDrawing graph}

theorem surgery_mixed_endpoints_ne (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (p q : C.InnerIndex) (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1) :
    D'.vertex (graph.src p.1) ≠ D'.vertex (graph.dst q.1) := by
  intro h
  have he := D'.vertex_injective h
  rcases hadj with hs | ht
  · exact graph.loopless q.1 (hs.symm.trans he)
  · exact graph.loopless p.1 (he.trans ht.symm)

end Paper170Geometry

end
end

section

/-! Actual drawing prefixes and suffixes meet vertices only at their retained endpoint. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}

namespace ExteriorCrossingCut
variable {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {r : C.InnerIndex}

theorem first_parameter_lt_one (K : ExteriorCrossingCut C P r) : (P r.1).knot K.first < 1 := by
  rw [← (P r.1).last]
  exact (P r.1).increasing (K.ordered.trans_le (Fin.le_last _))

theorem last_parameter_pos (K : ExteriorCrossingCut C P r) : 0 < (P r.1).knot K.last := by
  rw [← (P r.1).first]
  exact (P r.1).increasing ((Fin.zero_le K.first).trans_lt K.ordered)

theorem prefix_vertex_eq (K : ExteriorCrossingCut C P r) (v : Vertex)
    (hv : D'.vertex v ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val))) :
    v=(graph.src r.1) := by
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hv
  rcases drawing_edge_vertex_parameter D'.toContinuousDrawing r.1 t v he with ⟨_,hv⟩ | ⟨ht1,_⟩
  · exact hv
  · exact False.elim ((ht1 ▸ ht.2).not_gt K.first_parameter_lt_one)

theorem suffix_vertex_eq (K : ExteriorCrossingCut C P r) (v : Vertex)
    (hv : D'.vertex v ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val))) :
    v=(graph.dst r.1) := by
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hv
  rcases drawing_edge_vertex_parameter D'.toContinuousDrawing r.1 t v he with ⟨ht0,_⟩ | ⟨_,hv⟩
  · exact False.elim ((ht0 ▸ ht.1).not_gt K.last_parameter_pos)
  · exact hv

end ExteriorCrossingCut
end Paper170Geometry

end
end

section

/-! Actual retained cuts are disjoint and contain only their own boundary port. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.ExteriorCrossingCut
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {r : C.InnerIndex}

theorem first_parameter_point (K : ExteriorCrossingCut C P r) :
    D'.edge r.1 ((P r.1).knot K.first)=C.portPoint (C.incomingPort r) :=
  ((drawingEdgeWalk_getVert P r.1 K.first.val (by have h := K.first.isLt; omega)).trans
    ((P r.1).vertices_at K.first)).symm.trans K.first_point

theorem last_parameter_point (K : ExteriorCrossingCut C P r) :
    D'.edge r.1 ((P r.1).knot K.last)=C.portPoint (C.outgoingPort r) :=
  ((drawingEdgeWalk_getVert P r.1 K.last.val (by have h := K.last.isLt; omega)).trans
    ((P r.1).vertices_at K.last)).symm.trans K.last_point

theorem prefix_subset_edge (K : ExteriorCrossingCut C P r) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) ⊆ Set.range (D'.edge r.1) := by
  intro x hx
  obtain ⟨t,_,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  exact ⟨t,he⟩

theorem suffix_subset_edge (K : ExteriorCrossingCut C P r) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) ⊆ Set.range (D'.edge r.1) := by
  intro x hx
  obtain ⟨t,_,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hx
  exact ⟨t,he⟩

theorem incoming_not_suffix (K : ExteriorCrossingCut C P r) :
    C.portPoint (C.incomingPort r) ∉ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) := by
  intro hx
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hx
  have heq := D'.edge_injective r.1 (he.trans K.first_parameter_point.symm)
  exact ((P r.1).increasing K.ordered).not_ge (heq ▸ ht.1)

theorem outgoing_not_prefix (K : ExteriorCrossingCut C P r) :
    C.portPoint (C.outgoingPort r) ∉ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) := by
  intro hx
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  have heq := D'.edge_injective r.1 (he.trans K.last_parameter_point.symm)
  exact ((P r.1).increasing K.ordered).not_ge (heq ▸ ht.2)

theorem prefix_suffix_disjoint (K : ExteriorCrossingCut C P r) :
    Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  obtain ⟨u,hu,hf⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hy
  have heq := D'.edge_injective r.1 (he.trans hf.symm)
  exact ((P r.1).increasing K.ordered).not_ge (hu.1.trans (heq ▸ ht.2))

end Paper170Geometry.ExteriorCrossingCut

end
end

end OAI
