import OAI.Combinatorics.CompleteCrossing.DiskChords

namespace OAI

/-! Continuous assembled edges, their incidences, crossings, and absence of triple points. -/

section

/-! Actual simple replacement edges, including both graph-vertex spokes. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

def startSpoke (C : DrawingPassages D) (v : Vertex → Plane) (e : Edge) :
    Path (v (graph.src e)) (C.arcStart (C.firstArc e)) := Path.segment _ _

def endSpoke (C : DrawingPassages D) (v : Vertex → Plane) (e : Edge) :
    Path (C.arcEnd (C.lastArc e)) (v (graph.dst e)) := (Path.segment _ _).symm

def assembledEdge (E : PolygonalExterior C) (v : Vertex → Plane)
    (e : Edge) : Path (v (graph.src e)) (v (graph.dst e)) :=
  ((startSpoke C v e).trans (E.anchoredMiddle e)).trans (endSpoke C v e)

theorem startSpoke_injective (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge) :
    Function.Injective (startSpoke C v e) := C.vertex_spoke_injective v hv _ (C.startPortAt e)

theorem endSpoke_range (v : Vertex → Plane) (e : Edge) :
    Set.range (endSpoke C v e)=Set.range (Path.segment (v (graph.dst e)) (C.portPoint (C.endPortAt e).val)) := by
  exact Path.symm_range _

theorem endSpoke_injective (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge) :
    Function.Injective (endSpoke C v e) := by
  intro s t he
  have hh := C.vertex_spoke_injective v hv _ (C.endPortAt e) he
  have hval := congrArg Subtype.val hh
  apply Subtype.ext
  change 1-s.val=1-t.val at hval
  linarith

theorem assembledEdge_injective (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge) :
    Function.Injective (E.assembledEdge v e) := by
  have hfirst : Function.Injective ((startSpoke C v e).trans (E.anchoredMiddle e)) := by
    apply path_trans_injective _ _ (startSpoke_injective v hv e) (E.anchoredMiddle_injective e)
    intro x hx hy
    exact E.middle_spoke_meeting v hv e _ (C.startPortAt e) x hy hx
  apply path_trans_injective _ _ hfirst (endSpoke_injective v hv e)
  intro x hx hy
  rw [Path.trans_range] at hx
  rw [endSpoke_range] at hy
  rcases hx with hx | hx
  · have hd := C.vertex_spokes_disjoint_of_vertices_ne v hv (graph.src e) (graph.dst e)
      (graph.loopless e) (C.startPortAt e) (C.endPortAt e)
    exact False.elim (Set.disjoint_left.mp hd hx hy)
  · exact E.middle_spoke_meeting v hv e _ (C.endPortAt e) x hx hy

theorem assembledEdge_range_iff (E : PolygonalExterior C) (v : Vertex → Plane)
    (e : Edge) (x : Plane) :
    x ∈ Set.range (E.assembledEdge v e) ↔
      (x ∈ Set.range (startSpoke C v e) ∨
        (∃ i : C.ArcIndex, i.1=e ∧ x ∈ Set.range (E.chain i).path) ∨
        (∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p))) ∨
      x ∈ Set.range (endSpoke C v e) := by
  simp only [assembledEdge,Path.trans_range,Set.mem_union,anchoredMiddle_range,E.middlePath_range_iff]

end Paper170Geometry.PolygonalExterior

end
end

section

/-! The assembled replacement is an actual continuous drawing with simple, vertex-avoiding edges. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem vertex_spoke_vertex_eq (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j k : Vertex) (p : C.PortsAt (C.vertexMark j))
    (hk : v k ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : k=j := by
  by_contra hkj
  have hd := C.disks_disjoint _ _ (C.vertexMark_injective.ne (Ne.symm hkj))
  exact Set.disjoint_left.mp hd (C.vertex_spoke_range_in_disk v hv j p hk) (hv k).le

end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem middlePath_avoids_vertices (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge)
    (j : Vertex) : v j ∉ Set.range (E.middlePath e) := by
  intro hx
  rcases (E.middlePath_range_iff e (v j)).mp hx with ⟨i,hi,⟨t,ht⟩⟩ | ⟨p,hp,hx⟩
  · exact E.avoids_new_vertices v hv i t j ht
  · exact Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks p j) hx (hv j).le

theorem assembledEdge_vertex_eq (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge)
    (j : Vertex) (hj : v j ∈ Set.range (E.assembledEdge v e)) :
    j=graph.src e ∨ j=graph.dst e := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hj
  rcases hj with (hj | hj) | hj
  · exact Or.inl (C.vertex_spoke_vertex_eq v hv _ j (C.startPortAt e) hj)
  · exact False.elim (E.middlePath_avoids_vertices v hv e j hj)
  · rw [endSpoke_range] at hj
    exact Or.inr (C.vertex_spoke_vertex_eq v hv _ j (C.endPortAt e) hj)

theorem assembledEdge_interior_avoids_vertices (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1)
    (j : Vertex) : E.assembledEdge v e t ≠ v j := by
  intro he
  rcases E.assembledEdge_vertex_eq v hv e j ⟨t,he⟩ with rfl | rfl
  · have hh := E.assembledEdge_injective v hv e (he.trans (E.assembledEdge v e).source.symm)
    exact ht.1.ne hh.symm
  · have hh := E.assembledEdge_injective v hv e (he.trans (E.assembledEdge v e).target.symm)
    exact ht.2.ne hh

def assembledDrawing (E : PolygonalExterior C) (v : Vertex → Plane)
    (hvinj : Function.Injective v) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) :
    Paper170.ContinuousDrawing graph where
  vertex := v
  vertex_injective := hvinj
  edge := E.assembledEdge v
  edge_injective := E.assembledEdge_injective v hv
  interior_avoids_vertices := E.assembledEdge_interior_avoids_vertices v hv

theorem exists_assembledDrawing [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) :
    ∃ (C : DrawingPassages D) (E : PolygonalExterior C)
      (v : Vertex → Plane) (hvinj : Function.Injective v)
      (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2),
      ∀ e, Function.Injective ((E.assembledDrawing v hvinj hv).edge e) := by
  obtain ⟨C⟩ := nonempty_drawingPassages D
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  exact ⟨C,E,v,hvinj,hv,E.assembledEdge_injective v hv⟩

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Cross-edge incidence of the actual middle paths and exterior pieces. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem middle_exterior_edge_eq (E : PolygonalExterior C) (e : Edge)
    (i : C.ArcIndex) (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (E.chain i).path) : e=i.1 := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨j,hj,hx⟩ | ⟨p,hp,hx⟩
  · have he : j=i := by
      by_contra hji
      exact Set.disjoint_left.mp (E.disjoint j i hji) hx hy
    exact hj.symm.trans (congrArg Sigma.fst he)
  · obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    rcases E.exterior_chord_meeting_parameters i p s t (hs.trans ht.symm) with
      ⟨hi,_,_⟩ | ⟨hi,_,_⟩
    · exact hp.symm.trans (congrArg Sigma.fst hi).symm
    · exact hp.symm.trans (congrArg Sigma.fst hi).symm

theorem middle_spoke_edge_eq (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
    (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : e=p.val.1.1 := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,⟨s,hs⟩⟩ | ⟨q,hq,hx⟩
  · obtain ⟨t,ht⟩ := hy
    have hm := E.exterior_spoke_meeting_parameters v hv i j p s t (hs.trans ht.symm)
    rcases hm.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact hi.symm.trans (congrArg (fun r : C.Port => r.1.1) he)
    · exact hi.symm.trans (congrArg (fun r : C.Port => r.1.1) he)
  · exact False.elim (Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks q j)
      hx (C.vertex_spoke_range_in_disk v hv j p hy))

theorem middle_middle_meeting_chords (E : PolygonalExterior C) (e f : Edge)
    (hef : e ≠ f) (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (E.middlePath f)) :
    ∃ p q : C.InnerIndex, p.1=e ∧ q.1=f ∧
      x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q) := by
  have he : ∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p) := by
    rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,hh⟩ | hh
    · exact False.elim (hef ((E.middle_exterior_edge_eq f i x hy hh).trans hi).symm)
    · exact hh
  have hf : ∃ q : C.InnerIndex, q.1=f ∧ x ∈ Set.range (C.crossingChord q) := by
    rcases (E.middlePath_range_iff f x).mp hy with ⟨i,hi,hh⟩ | hh
    · exact False.elim (hef ((E.middle_exterior_edge_eq e i x hx hh).trans hi))
    · exact hh
  obtain ⟨p,hp,hxp⟩ := he
  obtain ⟨q,hq,hxq⟩ := hf
  exact ⟨p,q,hp,hq,hxp,hxq⟩

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Every nonvertex intersection of assembled edges is an actual crossing-disk chord intersection. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem vertex_spokes_meeting (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (j k : Vertex) (p : C.PortsAt (C.vertexMark j)) (q : C.PortsAt (C.vertexMark k))
    (hpq : p.val ≠ q.val) (x : Plane)
    (hx : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val)))
    (hy : x ∈ Set.range (Path.segment (v k) (C.portPoint q.val))) : x=v j := by
  by_cases hjk : j=k
  · subst k
    exact spokes_meet_only_at_center _ _ _ (hdet j p q (fun he => hpq (congrArg Subtype.val he)))
      (by simpa only [Path.range_segment] using hx) (by simpa only [Path.range_segment] using hy)
  · exact False.elim (Set.disjoint_left.mp (C.vertex_spokes_disjoint_of_vertices_ne v hv j k hjk p q) hx hy)

end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_spoke_meeting (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e : Edge) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
    (hep : e ≠ p.val.1.1) (x : Plane) (hx : x ∈ Set.range (E.assembledEdge v e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : x=v j := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hx
  rcases hx with (hx | hx) | hx
  · exact C.vertex_spokes_meeting v hv hdet j _ p (C.startPortAt e)
      (fun he => hep (congrArg (fun r : C.Port => r.1.1) he).symm) x hy hx
  · exact False.elim (hep (E.middle_spoke_edge_eq v hv e j p x hx hy))
  · rw [endSpoke_range] at hx
    exact C.vertex_spokes_meeting v hv hdet j _ p (C.endPortAt e)
      (fun he => hep (congrArg (fun r : C.Port => r.1.1) he).symm) x hy hx

theorem assembled_meeting_chords (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : Edge) (hef : e ≠ f) (x : Plane)
    (havoid : ∀ j, x ≠ v j) (hx : x ∈ Set.range (E.assembledEdge v e))
    (hy : x ∈ Set.range (E.assembledEdge v f)) :
    ∃ p q : C.InnerIndex, p.1=e ∧ q.1=f ∧
      x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q) := by
  have hm (a b : Edge) (hab : a ≠ b)
      (ha : x ∈ Set.range (E.assembledEdge v a)) (hb : x ∈ Set.range (E.assembledEdge v b)) :
      x ∈ Set.range (E.middlePath a) := by
    rw [assembledEdge,Path.trans_range,Path.trans_range] at ha
    rcases ha with (ha | ha) | ha
    · exact False.elim (havoid _ (E.assembled_spoke_meeting v hv hdet b _ (C.startPortAt a)
        (Ne.symm hab) x hb ha))
    · exact ha
    · rw [endSpoke_range] at ha
      exact False.elim (havoid _ (E.assembled_spoke_meeting v hv hdet b _ (C.endPortAt a)
        (Ne.symm hab) x hb ha))
  exact E.middle_middle_meeting_chords e f hef x (hm e f hef hx hy) (hm f e (Ne.symm hef) hy hx)

theorem assembled_crossings_subset (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    Paper170.crossingPoints (E.assembledDrawing v hvinj hv) ⊆ C.chordCrossings := by
  rintro x ⟨e,f,hef,⟨s,hs,he⟩,⟨t,ht,hf⟩⟩
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq))
    ⟨s,he⟩ ⟨t,hf⟩
  exact ⟨p,q,(fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))),hxp,hxq⟩

theorem assembled_crossings_finite (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    (Paper170.crossingPoints (E.assembledDrawing v hvinj hv)).Finite :=
  C.chordCrossings_finite.subset (E.assembled_crossings_subset v hvinj hv hdet)

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! No triple intersection is introduced by the actual replacement drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_no_triples (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f g : Edge) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e ∩
      Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f ∩
      Paper170.edgeInterior (E.assembledDrawing v hvinj hv) g=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨⟨⟨s,hs,he⟩,⟨t,ht,hf⟩⟩,⟨u,hu,hg⟩⟩
  have ha : ∀ j, x ≠ v j := fun j heq =>
    E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x ha ⟨s,he⟩ ⟨t,hf⟩
  obtain ⟨r,z,hr,hz,hxr,hxz⟩ := E.assembled_meeting_chords v hv hdet e g heg x ha ⟨s,he⟩ ⟨u,hg⟩
  apply C.innerMark_no_triples p q z
  · intro heq
    exact hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  · intro heq
    exact heg (hp.symm.trans ((congrArg Sigma.fst heq).trans hz))
  · intro heq
    exact hfg (hq.symm.trans ((congrArg Sigma.fst heq).trans hz))
  · exact C.chord_meeting_marks_eq p q hxp hxq
  · exact C.chord_meeting_marks_eq p z hxp hxz

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Each actual boundary port belongs to exactly its assigned assembled edge. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem portPoint_mem_exterior (E : PolygonalExterior C) (p : C.Port) :
    C.portPoint p ∈ Set.range (E.chain p.1).path := by
  rcases p with ⟨i,b⟩
  cases b
  · exact ⟨0,(E.chain i).path.source⟩
  · exact ⟨1,(E.chain i).path.target⟩

theorem assembled_port_mem_range (E : PolygonalExterior C) (v : Vertex → Plane)
    (p : C.Port) : C.portPoint p ∈ Set.range (E.assembledEdge v p.1.1) := by
  apply (E.assembledEdge_range_iff v p.1.1 (C.portPoint p)).mpr
  exact Or.inl (Or.inr (Or.inl ⟨p.1,rfl,E.portPoint_mem_exterior p⟩))

theorem assembled_exterior_edge_eq (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (i : C.ArcIndex) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hy : x ∈ Set.range (E.chain i).path) : e=i.1 := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    have hh := E.exterior_spoke_meeting_parameters v hv i _ (C.startPortAt e) s t (hs.trans ht.symm)
    rcases hh.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
  · exact E.middle_exterior_edge_eq e i x hx hy
  · rw [endSpoke_range] at hx
    obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    have hh := E.exterior_spoke_meeting_parameters v hv i _ (C.endPortAt e) s t (hs.trans ht.symm)
    rcases hh.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm

theorem assembled_port_unique_edge (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (p : C.Port)
    (hp : C.portPoint p ∈ Set.range (E.assembledEdge v e)) : e=p.1.1 :=
  E.assembled_exterior_edge_eq v hv e p.1 (C.portPoint p) hp (E.portPoint_mem_exterior p)

end Paper170Geometry.PolygonalExterior

end
end

end OAI
