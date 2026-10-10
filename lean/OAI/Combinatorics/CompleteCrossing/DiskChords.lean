import OAI.Combinatorics.CompleteCrossing.DiskFilling
import OAI.Combinatorics.Crossing.AlternatingPaths
import OAI.Combinatorics.Crossing.SimultaneousExteriorArcs

namespace OAI

/-! Exterior polygonal replacement, ordered passages, and injective middle paths. -/

section

/-! Appendix A's exterior replacement, derived from the actual admissible drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem drawing_exterior_polygonal_replacement [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) :
    ∃ C : DrawingPassages D, ∃ U : C.ArcIndex → Set Plane,
      ∃ P : ∀ i, PolygonalChain (U i) (C.arcStart i) (C.arcEnd i),
        (∀ i, IsOpen (U i)) ∧ (∀ i, Function.Injective (P i).path) ∧
        (∀ i t, t ∈ Set.Ioo (0 : unitInterval) 1 →
          (P i).path t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius) ∧
        (∀ i j, i ≠ j → Disjoint (Set.range (P i).path) (Set.range (P j).path)) := by
  classical
  obtain ⟨C⟩ := nonempty_drawingPassages D
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  obtain ⟨U,P,hU,hP,hout,hdisjoint⟩ := finite_exterior_arc_replacements
    (fun x : DrawingMark D => x.val) C.radius C.radius_pos C.disks_disjoint
    C.arcStartMark C.arcEndMark C.arcStart C.arcEnd C.arc_endpoints_ne
    C.arc_start_on_circle C.arc_end_on_circle C.arc C.arcs_pairwise_disjoint C.arc_interior_outside
  exact ⟨C,U,P,hU,hP,hout,hdisjoint⟩

end Paper170Geometry

end
end

section

/-! Constructed polygonal exterior paths, packaged with their actual geometric properties. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
variable  {D : FiniteIntersectionDrawing graph}

structure PolygonalExterior (C : DrawingPassages D) where
  chain : ∀ i : C.ArcIndex, PolygonalChain Set.univ (C.arcStart i) (C.arcEnd i)
  injective : ∀ i, Function.Injective (chain i).path
  outside : ∀ i t, t ∈ Set.Ioo (0 : unitInterval) 1 →
    (chain i).path t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius
  disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (chain i).path) (Set.range (chain j).path)

theorem nonempty_polygonalExterior [Fintype Vertex] [Fintype Edge] (C : DrawingPassages D) : Nonempty (PolygonalExterior C) := by
  classical
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  obtain ⟨U,P,hU,hP,hout,hdisjoint⟩ := finite_exterior_arc_replacements
    (fun x : DrawingMark D => x.val) C.radius C.radius_pos C.disks_disjoint
    C.arcStartMark C.arcEndMark C.arcStart C.arcEnd C.arc_endpoints_ne
    C.arc_start_on_circle C.arc_end_on_circle C.arc C.arcs_pairwise_disjoint C.arc_interior_outside
  exact ⟨{
    chain := fun i => (P i).widen (Set.subset_univ _)
    injective := hP
    outside := hout
    disjoint := hdisjoint }⟩

namespace PolygonalExterior
variable {C : DrawingPassages D}

theorem outside_open_disks (E : PolygonalExterior C) (i : C.ArcIndex) (t : unitInterval)
    (x : DrawingMark D) : C.radius^2 ≤ squaredLength ((E.chain i).path t-x.val) := by
  by_cases ht0 : t=0
  · subst t
    rw [(E.chain i).path.source]
    exact C.portPoint_outside_open_disks (i,false) x
  by_cases ht1 : t=1
  · subst t
    rw [(E.chain i).path.target]
    exact C.portPoint_outside_open_disks (i,true) x
  exact (E.outside i t ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩ x).le

theorem avoids_new_vertices (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : C.ArcIndex) (t : unitInterval) (j : Vertex) : (E.chain i).path t ≠ v j := by
  intro he
  have h := E.outside_open_disks i t (C.vertexMark j)
  rw [he] at h
  exact (hv j).not_ge h

theorem parameter_endpoint_of_mem_disk (E : PolygonalExterior C) (i : C.ArcIndex)
    (t : unitInterval) (x : DrawingMark D)
    (ht : (E.chain i).path t ∈ closedRoundDisk x.val C.radius) : t=0 ∨ t=1 := by
  by_cases h0 : t=0
  · exact Or.inl h0
  by_cases h1 : t=1
  · exact Or.inr h1
  have h := E.outside i t ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm h0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) h1⟩ x
  exact False.elim (h.not_ge ht)

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Exterior pieces and crossing chords meet only at their assigned endpoint joins. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem chord_parameter_endpoint (E : PolygonalExterior C) (i : C.ArcIndex) (p : C.InnerIndex)
    (s t : unitInterval) (he : (E.chain i).path s=C.crossingChord p t) : t=0 ∨ t=1 := by
  by_cases ht0 : t=0
  · exact Or.inl ht0
  by_cases ht1 : t=1
  · exact Or.inr ht1
  have h := C.crossingChord_interior_in_disk p t
    ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩
  have hx := E.outside_open_disks i s (C.innerMark p)
  rw [he] at hx
  exact False.elim (h.not_ge hx)

theorem exterior_chord_meeting_parameters (E : PolygonalExterior C) (i : C.ArcIndex) (p : C.InnerIndex)
    (s t : unitInterval) (he : (E.chain i).path s=C.crossingChord p t) :
    (i=C.incomingArc p ∧ s=1 ∧ t=0) ∨ (i=C.outgoingArc p ∧ s=0 ∧ t=1) := by
  have hs := E.parameter_endpoint_of_mem_disk i s (C.innerMark p) (by
    rw [he]
    exact C.crossingChord_range_subset_disk p ⟨t,rfl⟩)
  have ht := E.chord_parameter_endpoint i p s t he
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · simp only [Path.source] at he
    have hp : (i,false)=C.incomingPort p := C.portPoint_injective he
    have hh : false=true := congrArg Prod.snd hp
    cases hh
  · simp only [Path.source,Path.target] at he
    have hp : (i,false)=C.outgoingPort p := C.portPoint_injective he
    exact Or.inr ⟨congrArg Prod.fst hp,rfl,rfl⟩
  · simp only [Path.source,Path.target] at he
    have hp : (i,true)=C.incomingPort p := C.portPoint_injective he
    exact Or.inl ⟨congrArg Prod.fst hp,rfl,rfl⟩
  · simp only [Path.target] at he
    have hp : (i,true)=C.outgoingPort p := C.portPoint_injective he
    have hh : true=false := congrArg Prod.snd hp
    cases hh

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Exterior paths meet vertex spokes only at their assigned boundary endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem exterior_spoke_meeting_parameters (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (i : C.ArcIndex) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
    (s t : unitInterval) (he : (E.chain i).path s=(Path.segment (v j) (C.portPoint p.val)) t) :
    t=1 ∧ ((s=0 ∧ (i,false)=p.val) ∨ (s=1 ∧ (i,true)=p.val)) := by
  have ht : t=1 := by
    apply le_antisymm (show t ≤ 1 from t.property.2)
    apply le_of_not_gt
    intro ht1
    have hinside := C.vertex_spoke_interior v hv j p t ht1
    have hout := E.outside_open_disks i s (C.vertexMark j)
    rw [he] at hout
    exact hinside.not_ge hout
  subst t
  rw [Path.target] at he
  have hs := E.parameter_endpoint_of_mem_disk i s (C.vertexMark j) (by
    rw [he]
    exact (C.portsAt_on_circle (C.vertexMark j) p).le)
  refine ⟨rfl,?_⟩
  rcases hs with rfl | rfl
  · rw [Path.source] at he
    exact Or.inl ⟨rfl,C.portPoint_injective he⟩
  · rw [Path.target] at he
    exact Or.inr ⟨rfl,C.portPoint_injective he⟩

end Paper170Geometry.PolygonalExterior

end
end

section

/-! Ordered actual exterior paths and the internal chords of a fixed edge. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

def orderedArc (C : DrawingPassages D) (e : Edge) (i : ℕ) : C.ArcIndex :=
  ⟨e,⟨min i (C.count e-1),by have h := C.count_pos e; omega⟩⟩

theorem orderedArc_val (C : DrawingPassages D) (e : Edge) (i : ℕ)
    (hi : i < C.count e) : (C.orderedArc e i).2.val=i := by
  change min i (C.count e-1)=i
  omega

theorem orderedArc_inj (C : DrawingPassages D) (e : Edge) (i j : ℕ)
    (hi : i < C.count e) (hj : j < C.count e)
    (h : C.orderedArc e i=C.orderedArc e j) : i=j := by
  have hh := congrArg (fun p : C.ArcIndex => p.2.val) h
  simpa only [C.orderedArc_val e i hi,C.orderedArc_val e j hj] using hh

theorem orderedArc_first (C : DrawingPassages D) (e : Edge) :
    C.orderedArc e 0=C.firstArc e := by
  simp [orderedArc,firstArc]

theorem orderedArc_last (C : DrawingPassages D) (e : Edge) :
    C.orderedArc e (C.count e-1)=C.lastArc e := by
  simp [orderedArc,lastArc]

def orderedInner (C : DrawingPassages D) (e : Edge) (j : ℕ)
    (hj : j+1 < C.count e) : C.InnerIndex :=
  ⟨e,⟨⟨j+1,by omega⟩,⟨Nat.succ_pos j,hj⟩⟩⟩

theorem orderedInner_incoming (C : DrawingPassages D) (e : Edge)
    (j : ℕ) (hj : j+1 < C.count e) :
    C.incomingArc (C.orderedInner e j hj)=C.orderedArc e j := by
  unfold incomingArc orderedInner orderedArc
  congr 1
  apply Fin.ext
  change j+1-1=min j (C.count e-1)
  omega

theorem orderedInner_outgoing (C : DrawingPassages D) (e : Edge)
    (j : ℕ) (hj : j+1 < C.count e) :
    C.outgoingArc (C.orderedInner e j hj)=C.orderedArc e (j+1) := by
  unfold outgoingArc orderedInner orderedArc
  congr 1
  apply Fin.ext
  change j+1=min (j+1) (C.count e-1)
  omega

theorem orderedInner_inj (C : DrawingPassages D) (e : Edge) (i j : ℕ)
    (hi : i+1 < C.count e) (hj : j+1 < C.count e)
    (h : C.orderedInner e i hi=C.orderedInner e j hj) : i=j := by
  have hh : i+1=j+1 := congrArg (fun p : C.InnerIndex => p.2.val.val) h
  omega

end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

def orderedPath (E : PolygonalExterior C) (e : Edge) (i : ℕ) :
    Path (C.arcStart (C.orderedArc e i)) (C.arcEnd (C.orderedArc e i)) :=
  (E.chain (C.orderedArc e i)).path

def orderedBridge (C : DrawingPassages D) (e : Edge) (i : ℕ) :
    Path (C.arcEnd (C.orderedArc e i)) (C.arcStart (C.orderedArc e (i+1))) := Path.segment _ _

theorem orderedBridge_apply (e : Edge) (j : ℕ) (hj : j+1 < C.count e)
    (t : unitInterval) :
    orderedBridge C e j t=C.crossingChord (C.orderedInner e j hj) t := by
  change (Path.segment _ _ : Path _ _) t=(Path.segment _ _ : Path _ _) t
  have ha : C.portPoint (C.incomingPort (C.orderedInner e j hj))=C.arcEnd (C.orderedArc e j) := by
    change C.arcEnd (C.incomingArc (C.orderedInner e j hj))=_
    rw [C.orderedInner_incoming]
  have hb : C.portPoint (C.outgoingPort (C.orderedInner e j hj))=C.arcStart (C.orderedArc e (j+1)) := by
    change C.arcStart (C.outgoingArc (C.orderedInner e j hj))=_
    rw [C.orderedInner_outgoing]
  simp only [Path.segment_apply,ha,hb]

theorem orderedBridge_range (e : Edge) (j : ℕ) (hj : j+1 < C.count e) :
    Set.range (orderedBridge C e j)=Set.range (C.crossingChord (C.orderedInner e j hj)) := by
  congr 1
  funext t
  exact orderedBridge_apply e j hj t

def middlePath (E : PolygonalExterior C) (e : Edge) :
    Path (C.arcStart (C.orderedArc e 0)) (C.arcEnd (C.orderedArc e (C.count e-1))) :=
  alternatingPath (fun i => C.arcStart (C.orderedArc e i))
    (fun i => C.arcEnd (C.orderedArc e i)) (E.orderedPath e) (orderedBridge C e) (C.count e-1)

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! The actual ordered replacement of an edge between its first and last boundary ports is simple. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem middlePath_injective (E : PolygonalExterior C) (e : Edge) :
    Function.Injective (E.middlePath e) := by
  have hc := C.count_pos e
  apply alternatingPath_injective
  · intro i hi
    exact E.injective _
  · intro j hj
    have h := C.crossingChord_injective (C.orderedInner e j (by omega))
    intro s t he
    apply h
    simpa only [orderedBridge_apply (C:=C) e j (by omega)] using he
  · intro i j hi hj hij
    exact E.disjoint _ _ (fun he => hij (C.orderedArc_inj e i j (by omega) (by omega) he))
  · intro i j hi hj hij
    rw [orderedBridge_range e i (by omega),orderedBridge_range e j (by omega)]
    apply C.crossingChords_disjoint_of_marks_ne
    intro he
    apply hij
    apply C.orderedInner_inj e i j
    exact C.innerIndex_eq_of_edge_mark _ _ rfl he
  · intro i j hi hj x hx hy
    obtain ⟨s,hs⟩ := hx
    obtain ⟨t,ht⟩ := hy
    have hbridge := orderedBridge_apply (C:=C) e j (by omega) t
    have hm := E.exterior_chord_meeting_parameters (C.orderedArc e i)
      (C.orderedInner e j (by omega)) s t (hs.trans (ht.symm.trans hbridge))
    rcases hm with ⟨he,rfl,rfl⟩ | ⟨he,rfl,rfl⟩
    · rw [C.orderedInner_incoming] at he
      have hij := C.orderedArc_inj e i j (by omega) (by omega) he
      refine Or.inl ⟨hij,?_⟩
      subst i
      exact hs.symm.trans (E.orderedPath e j).target
    · rw [C.orderedInner_outgoing] at he
      have hij := C.orderedArc_inj e i (j+1) (by omega) (by omega) he
      refine Or.inr ⟨hij,?_⟩
      subst i
      exact hs.symm.trans (E.orderedPath e (j+1)).source

theorem middlePath_range_iff (E : PolygonalExterior C) (e : Edge) (x : Plane) :
    x ∈ Set.range (E.middlePath e) ↔
      (∃ i : C.ArcIndex, i.1=e ∧ x ∈ Set.range (E.chain i).path) ∨
      (∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p)) := by
  have hc := C.count_pos e
  rw [middlePath,alternatingPath_range_iff]
  constructor
  · rintro (⟨i,hi,hx⟩ | ⟨j,hj,hx⟩)
    · exact Or.inl ⟨C.orderedArc e i,rfl,hx⟩
    · exact Or.inr ⟨C.orderedInner e j (by omega),rfl,
        by simpa only [orderedBridge_range (C:=C) e j (by omega)] using hx⟩
  · rintro (⟨⟨f,i⟩,he,hx⟩ | ⟨⟨f,⟨j,hj⟩⟩,he,hx⟩)
    · change f=e at he
      subst f
      refine Or.inl ⟨i.val,by omega,?_⟩
      have heq : C.orderedArc e i.val=⟨e,i⟩ := by
        unfold DrawingPassages.orderedArc
        congr 1
        apply Fin.ext
        change min i.val (C.count e-1)=i.val
        omega
      change x ∈ Set.range (E.chain (C.orderedArc e i.val)).path
      rw [heq]
      exact hx
    · change f=e at he
      subst f
      refine Or.inr ⟨j.val-1,by omega,?_⟩
      rw [orderedBridge_range e (j.val-1) (by omega)]
      have heq : C.orderedInner e (j.val-1) (by omega)=⟨e,⟨j,hj⟩⟩ := by
        unfold DrawingPassages.orderedInner
        congr 1
        apply Subtype.ext
        apply Fin.ext
        change j.val-1+1=j.val
        omega
      rw [heq]
      exact hx

end Paper170Geometry.PolygonalExterior

end
end

section

/-! A constructed middle path meets a vertex spoke only at its boundary port. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem vertex_spoke_range_in_disk (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j : Vertex) (p : C.PortsAt (C.vertexMark j)) :
    Set.range (Path.segment (v j) (C.portPoint p.val)) ⊆ closedRoundDisk (D.vertex j) C.radius := by
  rintro x ⟨t,rfl⟩
  by_cases ht : t=1
  · subst t
    rw [Path.target]
    exact (C.portsAt_on_circle (C.vertexMark j) p).le
  · exact (C.vertex_spoke_interior v hv j p t
      (lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht)).le

theorem vertex_spokes_disjoint_of_vertices_ne (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j k : Vertex) (hjk : j ≠ k)
    (p : C.PortsAt (C.vertexMark j)) (q : C.PortsAt (C.vertexMark k)) :
    Disjoint (Set.range (Path.segment (v j) (C.portPoint p.val)))
      (Set.range (Path.segment (v k) (C.portPoint q.val))) :=
  (C.disks_disjoint _ _ (C.vertexMark_injective.ne hjk)).mono
    (C.vertex_spoke_range_in_disk v hv j p) (C.vertex_spoke_range_in_disk v hv k q)

end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem middle_spoke_meeting (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
    (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : x=C.portPoint p.val := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,⟨s,hs⟩⟩ | ⟨q,hq,hx⟩
  · obtain ⟨t,ht⟩ := hy
    have he := E.exterior_spoke_meeting_parameters v hv i j p s t (hs.trans ht.symm)
    rw [he.1,Path.target] at ht
    exact ht.symm
  · exact False.elim (Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks q j)
      hx (C.vertex_spoke_range_in_disk v hv j p hy))

def anchoredMiddle (E : PolygonalExterior C) (e : Edge) :
    Path (C.arcStart (C.firstArc e)) (C.arcEnd (C.lastArc e)) :=
  (E.middlePath e).cast (congrArg C.arcStart (C.orderedArc_first e).symm)
    (congrArg C.arcEnd (C.orderedArc_last e).symm)

theorem anchoredMiddle_range (E : PolygonalExterior C) (e : Edge) :
    Set.range (E.anchoredMiddle e)=Set.range (E.middlePath e) := rfl

theorem anchoredMiddle_injective (E : PolygonalExterior C) (e : Edge) :
    Function.Injective (E.anchoredMiddle e) := E.middlePath_injective e

end PolygonalExterior
end Paper170Geometry

end
end

end OAI
