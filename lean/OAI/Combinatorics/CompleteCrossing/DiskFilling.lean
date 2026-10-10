import OAI.Combinatorics.CompleteCrossing.Ports
import OAI.Combinatorics.Crossing.RoundCircleChords
import OAI.Combinatorics.Crossing.SegmentIntersectionUnique
import OAI.Combinatorics.Crossing.VertexDiskSpokes

namespace OAI

/-! Interior disk passages, vertex ports, filling containment, and crossing uniqueness. -/

section

/-! The actual internal marked passages and their two boundary endpoints. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

abbrev InnerIndex (C : DrawingPassages D) :=
  (e : Edge) × {i : Fin (C.count e+1) // 0 < i.val ∧ i.val < C.count e}

def innerMark (C : DrawingPassages D) (p : C.InnerIndex) : DrawingMark D :=
  ⟨D.edge p.1 (C.node p.1 p.2.val),C.node_mark p.1 p.2.val⟩

def incomingArc (C : DrawingPassages D) (p : C.InnerIndex) : C.ArcIndex :=
  ⟨p.1,⟨p.2.val.val-1,by have h := p.2.property; omega⟩⟩

def outgoingArc (C : DrawingPassages D) (p : C.InnerIndex) : C.ArcIndex :=
  ⟨p.1,⟨p.2.val.val,p.2.property.2⟩⟩

def incomingPort (C : DrawingPassages D) (p : C.InnerIndex) : C.Port := (C.incomingArc p,true)
def outgoingPort (C : DrawingPassages D) (p : C.InnerIndex) : C.Port := (C.outgoingArc p,false)

theorem incoming_node (C : DrawingPassages D) (p : C.InnerIndex) :
    (C.incomingArc p).2.succ=p.2.val := by
  apply Fin.ext
  change p.2.val.val-1+1=p.2.val.val
  have h := p.2.property.1
  omega

theorem outgoing_node (C : DrawingPassages D) (p : C.InnerIndex) :
    (C.outgoingArc p).2.castSucc=p.2.val := rfl

theorem incomingPort_mark (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portMark (C.incomingPort p)=C.innerMark p := by
  apply Subtype.ext
  change D.edge p.1 (C.node p.1 (C.incomingArc p).2.succ)=D.edge p.1 (C.node p.1 p.2.val)
  rw [C.incoming_node]

theorem outgoingPort_mark (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portMark (C.outgoingPort p)=C.innerMark p := rfl

theorem incomingPort_point (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portPoint (C.incomingPort p)=D.edge p.1 (C.passage p.1 p.2.val).enter := by
  change D.edge p.1 (C.passage p.1 (C.incomingArc p).2.succ).enter=_
  rw [C.incoming_node]

theorem outgoingPort_point (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portPoint (C.outgoingPort p)=D.edge p.1 (C.passage p.1 p.2.val).leave := rfl

theorem inner_parameter_interior (C : DrawingPassages D) (p : C.InnerIndex) :
    C.node p.1 p.2.val ∈ Set.Ioo (0 : unitInterval) 1 := by
  constructor
  · rw [← C.first p.1]
    exact C.increasing p.1 (show (0 : Fin (C.count p.1+1)) < p.2.val from p.2.property.1)
  · rw [← C.last p.1]
    exact C.increasing p.1 (show p.2.val < Fin.last (C.count p.1) from p.2.property.2)

theorem innerMark_is_crossing (C : DrawingPassages D) (p : C.InnerIndex) :
    (C.innerMark p).val ∈ Paper170.crossingPoints D.toContinuousDrawing := by
  have hm := (C.innerMark p).property
  rcases hm with ⟨v,hv⟩ | hcross
  · exact False.elim (D.interior_avoids_vertices p.1 (C.node p.1 p.2.val)
      (C.inner_parameter_interior p) v hv.symm)
  · exact hcross

def crossingChord (C : DrawingPassages D) (p : C.InnerIndex) :
    Path (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) :=
  Path.segment _ _

theorem crossingChord_injective (C : DrawingPassages D) (p : C.InnerIndex) :
    Function.Injective (C.crossingChord p) := by
  apply Path.segment_injective_of_ne
  intro he
  rw [C.incomingPort_point,C.outgoingPort_point] at he
  exact (C.passage p.1 p.2.val).enter_lt_leave.ne (D.edge_injective p.1 he)

end Paper170Geometry.DrawingPassages

end
end

section

/-! Actual replacement vertices and all incident straight-spoke directions. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

def vertexMark (_C : DrawingPassages D) (v : Vertex) : DrawingMark D :=
  ⟨D.vertex v,Or.inl ⟨v,rfl⟩⟩

theorem vertexMark_injective (C : DrawingPassages D) : Function.Injective C.vertexMark := by
  intro v w he
  exact D.vertex_injective (congrArg Subtype.val he)

theorem exists_drawing_vertex_placement [Fintype Edge] (C : DrawingPassages D) :
    ∃ v : Vertex → Plane, Function.Injective v ∧
      (∀ i, squaredLength (v i-D.vertex i) < C.radius^2) ∧
      (∀ i (p : C.PortsAt (C.vertexMark i)), v i ≠ C.portPoint p.val) ∧
      (∀ i (p q : C.PortsAt (C.vertexMark i)), p ≠ q →
        det2 (C.portPoint p.val-v i) (C.portPoint q.val-v i) ≠ 0) := by
  classical
  have hex (i : Vertex) : ∃ v : Plane,
      squaredLength (v-D.vertex i) < C.radius^2 ∧
      (∀ p : C.PortsAt (C.vertexMark i), v ≠ C.portPoint p.val) ∧
      (∀ p q : C.PortsAt (C.vertexMark i), p ≠ q → det2 (C.portPoint p.val-v) (C.portPoint q.val-v) ≠ 0) :=
    exists_vertex_disk_point (D.vertex i) C.radius C.radius_pos
      (fun p : C.PortsAt (C.vertexMark i) => C.portPoint p.val)
      (C.portPoint_injective.comp Subtype.val_injective) (C.portsAt_on_circle (C.vertexMark i))
  choose v hv hne hdet using hex
  refine ⟨v,?_,hv,hne,hdet⟩
  intro i j he
  by_contra hij
  have hd := C.disks_disjoint (C.vertexMark i) (C.vertexMark j) (C.vertexMark_injective.ne hij)
  have hi : v i ∈ closedRoundDisk (C.vertexMark i).val C.radius := (hv i).le
  have hj : v j ∈ closedRoundDisk (C.vertexMark j).val C.radius := (hv j).le
  exact Set.disjoint_left.mp hd hi (he.symm ▸ hj)

theorem vertex_spoke_injective (C : DrawingPassages D) (v : Vertex → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : Vertex) (p : C.PortsAt (C.vertexMark i)) :
    Function.Injective (Path.segment (v i) (C.portPoint p.val)) := by
  apply Path.segment_injective_of_ne
  intro he
  have h := hv i
  have hp : squaredLength (C.portPoint p.val-D.vertex i)=C.radius^2 := C.portsAt_on_circle (C.vertexMark i) p
  rw [he,hp] at h
  exact lt_irrefl _ h

theorem vertex_spoke_interior (C : DrawingPassages D) (v : Vertex → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : Vertex) (p : C.PortsAt (C.vertexMark i)) (t : unitInterval)
    (ht : t < 1) : squaredLength ((Path.segment (v i) (C.portPoint p.val)) t-D.vertex i) < C.radius^2 := by
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact spoke_in_open_disk (D.vertex i) (v i) (C.portPoint p.val) C.radius (hv i)
    (C.portsAt_on_circle (C.vertexMark i) p) t.val ⟨t.property.1,ht⟩

end Paper170Geometry.DrawingPassages

end
end

section

/-! Actual crossing-disk chord incidence, with no triples inherited from the original drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem innerIndex_eq_of_edge_mark (C : DrawingPassages D) (p q : C.InnerIndex)
    (he : p.1=q.1) (hm : C.innerMark p=C.innerMark q) : p=q := by
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  change e=f at he
  subst f
  congr 1
  apply Subtype.ext
  exact (C.increasing e).injective (D.edge_injective e (congrArg Subtype.val hm))

theorem incomingPort_injective (C : DrawingPassages D) : Function.Injective C.incomingPort := by
  intro p q he
  apply C.innerIndex_eq_of_edge_mark p q (congrArg (fun x : C.Port => x.1.1) he)
  have hh := congrArg C.portMark he
  simpa only [C.incomingPort_mark] using hh

theorem outgoingPort_injective (C : DrawingPassages D) : Function.Injective C.outgoingPort := by
  intro p q he
  apply C.innerIndex_eq_of_edge_mark p q (congrArg (fun x : C.Port => x.1.1) he)
  have hh := congrArg C.portMark he
  simpa only [C.outgoingPort_mark] using hh

theorem incomingPort_ne_outgoingPort (C : DrawingPassages D) (p q : C.InnerIndex) :
    C.incomingPort p ≠ C.outgoingPort q := by
  intro he
  have hh : true=false := congrArg Prod.snd he
  cases hh

theorem incomingPoint_on_circle (C : DrawingPassages D) (p : C.InnerIndex) :
    squaredLength (C.portPoint (C.incomingPort p)-(C.innerMark p).val)=C.radius^2 := by
  simpa only [C.incomingPort_mark] using C.portPoint_on_circle (C.incomingPort p)

theorem outgoingPoint_on_circle (C : DrawingPassages D) (p : C.InnerIndex) :
    squaredLength (C.portPoint (C.outgoingPort p)-(C.innerMark p).val)=C.radius^2 := by
  simpa only [C.outgoingPort_mark] using C.portPoint_on_circle (C.outgoingPort p)

theorem crossing_chords_transverse_at_mark (C : DrawingPassages D) (p q : C.InnerIndex)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    SegmentPairTransverse (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) := by
  apply round_circle_chords_transverse (C.innerMark p).val _ _ _ _ C.radius
  · exact C.incomingPoint_on_circle p
  · exact C.outgoingPoint_on_circle p
  · simpa only [hm] using C.incomingPoint_on_circle q
  · simpa only [hm] using C.outgoingPoint_on_circle q
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p p)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort q q)
  · exact C.portPoint_injective.ne (C.incomingPort_injective.ne hpq)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p q)
  · exact C.portPoint_injective.ne (Ne.symm (C.incomingPort_ne_outgoingPort q p))
  · exact C.portPoint_injective.ne (C.outgoingPort_injective.ne hpq)

theorem innerMark_no_triples (C : DrawingPassages D) (p q r : C.InnerIndex)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpqM : C.innerMark p=C.innerMark q) (hprM : C.innerMark p=C.innerMark r) : False := by
  have heq : p.1 ≠ q.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hpqM)
  have her : p.1 ≠ r.1 := fun he => hpr (C.innerIndex_eq_of_edge_mark p r he hprM)
  have hqrM : C.innerMark q=C.innerMark r := hpqM.symm.trans hprM
  have hfr : q.1 ≠ r.1 := fun he => hqr (C.innerIndex_eq_of_edge_mark q r he hqrM)
  have hp : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing p.1 :=
    ⟨C.node p.1 p.2.val,C.inner_parameter_interior p,rfl⟩
  have hq : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing q.1 := by
    rw [hpqM]
    exact ⟨C.node q.1 q.2.val,C.inner_parameter_interior q,rfl⟩
  have hr : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing r.1 := by
    rw [hprM]
    exact ⟨C.node r.1 r.2.val,C.inner_parameter_interior r,rfl⟩
  have hmem : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing p.1 ∩
      Paper170.edgeInterior D.toContinuousDrawing q.1 ∩ Paper170.edgeInterior D.toContinuousDrawing r.1 := ⟨⟨hp,hq⟩,hr⟩
  rw [D.no_triples p.1 q.1 r.1 heq her hfr] at hmem
  exact hmem

end Paper170Geometry.DrawingPassages

end
end

section

/-! The actual first and last retained ports attach to the prescribed graph vertices. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

def firstArc (C : DrawingPassages D) (e : Edge) : C.ArcIndex :=
  ⟨e,⟨0,C.count_pos e⟩⟩

def lastArc (C : DrawingPassages D) (e : Edge) : C.ArcIndex :=
  ⟨e,⟨C.count e-1,by have h := C.count_pos e; omega⟩⟩

theorem lastArc_node (C : DrawingPassages D) (e : Edge) :
    (C.lastArc e).2.succ=Fin.last (C.count e) := by
  apply Fin.ext
  have h := C.count_pos e
  change C.count e-1+1=C.count e
  omega

theorem firstArc_mark (C : DrawingPassages D) (e : Edge) :
    C.arcStartMark (C.firstArc e)=C.vertexMark (graph.src e) := by
  apply Subtype.ext
  change D.edge e (C.node e 0)=D.vertex (graph.src e)
  rw [C.first,Path.source]

theorem lastArc_mark (C : DrawingPassages D) (e : Edge) :
    C.arcEndMark (C.lastArc e)=C.vertexMark (graph.dst e) := by
  apply Subtype.ext
  change D.edge e (C.node e (C.lastArc e).2.succ)=D.vertex (graph.dst e)
  rw [C.lastArc_node,C.last,Path.target]

def startPortAt (C : DrawingPassages D) (e : Edge) : C.PortsAt (C.vertexMark (graph.src e)) :=
  ⟨(C.firstArc e,false),C.firstArc_mark e⟩

def endPortAt (C : DrawingPassages D) (e : Edge) : C.PortsAt (C.vertexMark (graph.dst e)) :=
  ⟨(C.lastArc e,true),C.lastArc_mark e⟩

end Paper170Geometry.DrawingPassages

end
end

section

/-! Actual closed-disk containment and strict interior containment of disk fillings. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

theorem round_chord_in_disk (z a b : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    squaredLength (segmentPoint a b t-z) ≤ r^2 := by
  have he : squaredLength (segmentPoint a b t-z)=
      (1-t)*squaredLength (a-z)+t*squaredLength (b-z)-t*(1-t)*squaredLength (b-a) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hnon : 0 ≤ t*(1-t)*squaredLength (b-a) := by
    apply mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    dsimp [squaredLength]
    positivity
  rw [he,ha,hb]
  linarith

namespace DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem crossingChord_range_subset_disk (C : DrawingPassages D) (p : C.InnerIndex) :
    Set.range (C.crossingChord p) ⊆ closedRoundDisk (C.innerMark p).val C.radius := by
  rintro x ⟨t,rfl⟩
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) ≤ C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_disk _ _ _ _ (C.incomingPoint_on_circle p) (C.outgoingPoint_on_circle p) t.val t.property

theorem crossingChord_interior_in_disk (C : DrawingPassages D) (p : C.InnerIndex)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    squaredLength (C.crossingChord p t-(C.innerMark p).val) < C.radius^2 := by
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) < C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_open_disk _ _ _ _ (C.incomingPoint_on_circle p) (C.outgoingPoint_on_circle p)
    (C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p p)) t.val ht

theorem crossingChords_disjoint_of_marks_ne (C : DrawingPassages D) (p q : C.InnerIndex)
    (hm : C.innerMark p ≠ C.innerMark q) :
    Disjoint (Set.range (C.crossingChord p)) (Set.range (C.crossingChord q)) :=
  (C.disks_disjoint _ _ hm).mono (C.crossingChord_range_subset_disk p) (C.crossingChord_range_subset_disk q)

theorem portPoint_outside_other_disk (C : DrawingPassages D) (p : C.Port) (x : DrawingMark D)
    (hx : C.portMark p ≠ x) : C.radius^2 < squaredLength (C.portPoint p-x.val) := by
  apply lt_of_not_ge
  intro hh
  have hp : C.portPoint p ∈ closedRoundDisk (C.portMark p).val C.radius := (C.portPoint_on_circle p).le
  exact Set.disjoint_left.mp (C.disks_disjoint _ _ hx) hp hh

theorem portPoint_outside_open_disks (C : DrawingPassages D) (p : C.Port) (x : DrawingMark D) :
    C.radius^2 ≤ squaredLength (C.portPoint p-x.val) := by
  by_cases he : C.portMark p=x
  · have hp := C.portPoint_on_circle p
    rw [he] at hp
    exact hp.ge
  · exact (C.portPoint_outside_other_disk p x he).le

theorem crossingChord_avoids_vertex_disks (C : DrawingPassages D) (p : C.InnerIndex)
    (v : Vertex) :
    Disjoint (Set.range (C.crossingChord p)) (closedRoundDisk (D.vertex v) C.radius) := by
  have hn : C.innerMark p ≠ C.vertexMark v := by
    intro he
    exact crossing_not_vertex D (C.innerMark p).val (C.innerMark_is_crossing p) v (congrArg Subtype.val he)
  exact (C.disks_disjoint _ _ hn).mono (C.crossingChord_range_subset_disk p) Set.Subset.rfl

end DrawingPassages
end Paper170Geometry

end
end

section

/-! At most one actual chord crossing point in each original crossing disk. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem innerIndex_at_mark_pair (C : DrawingPassages D) (p q r : C.InnerIndex)
    (hpq : p ≠ q) (hpqM : C.innerMark p=C.innerMark q) (hprM : C.innerMark p=C.innerMark r) :
    r=p ∨ r=q := by
  by_cases hrp : r=p
  · exact Or.inl hrp
  by_cases hrq : r=q
  · exact Or.inr hrq
  exact False.elim (C.innerMark_no_triples p q r hpq (Ne.symm hrp) (Ne.symm hrq) hpqM hprM)

def chordCrossingsAt (C : DrawingPassages D) (w : DrawingMark D) : Set Plane :=
  {x | ∃ p q : C.InnerIndex, p ≠ q ∧ C.innerMark p=w ∧ C.innerMark q=w ∧
    x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q)}

theorem chordCrossingsAt_subsingleton (C : DrawingPassages D) (w : DrawingMark D) :
    (C.chordCrossingsAt w).Subsingleton := by
  rintro x ⟨p,q,hpq,hp,hq,hxp,hxq⟩ y ⟨r,s,hrs,hr,hs,hyr,hys⟩
  have hpm : C.innerMark p=C.innerMark q := hp.trans hq.symm
  have hrpair := C.innerIndex_at_mark_pair p q r hpq hpm (hp.trans hr.symm)
  have hspair := C.innerIndex_at_mark_pair p q s hpq hpm (hp.trans hs.symm)
  have hunique := transverse_segment_intersection_subsingleton _ _ _ _
    (C.crossing_chords_transverse_at_mark p q hpq hpm)
  rcases hrpair with rfl | rfl <;> rcases hspair with rfl | rfl
  · exact False.elim (hrs rfl)
  · exact hunique ⟨hxp,hxq⟩ ⟨hyr,hys⟩
  · exact hunique ⟨hxp,hxq⟩ ⟨hys,hyr⟩
  · exact False.elim (hrs rfl)

theorem chord_meeting_marks_eq (C : DrawingPassages D) (p q : C.InnerIndex) {x : Plane}
    (hp : x ∈ Set.range (C.crossingChord p)) (hq : x ∈ Set.range (C.crossingChord q)) :
    C.innerMark p=C.innerMark q := by
  by_contra h
  exact Set.disjoint_left.mp (C.crossingChords_disjoint_of_marks_ne p q h) hp hq

def chordCrossings (C : DrawingPassages D) : Set Plane :=
  {x | ∃ p q : C.InnerIndex, p ≠ q ∧ x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q)}

theorem chord_crossing_original_mark (C : DrawingPassages D) {x : Plane} (hx : x ∈ C.chordCrossings) :
    ∃ w : DrawingMark D, w.val ∈ Paper170.crossingPoints D.toContinuousDrawing ∧ x ∈ C.chordCrossingsAt w := by
  obtain ⟨p,q,hpq,hp,hq⟩ := hx
  refine ⟨C.innerMark p,C.innerMark_is_crossing p,p,q,hpq,rfl,?_,hp,hq⟩
  exact (C.chord_meeting_marks_eq p q hp hq).symm

end Paper170Geometry.DrawingPassages

end
end

section

/-! Count actual spatial chord crossings by their original crossing disks. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
open scoped Classical
variable  {D : FiniteIntersectionDrawing graph}

def chordCrossingOrigin (C : DrawingPassages D) (x : Plane) : Plane :=
  if hx : x ∈ C.chordCrossings then (C.chord_crossing_original_mark hx).choose.val else 0

theorem chordCrossingOrigin_mapsTo (C : DrawingPassages D) :
    Set.MapsTo C.chordCrossingOrigin C.chordCrossings (Paper170.crossingPoints D.toContinuousDrawing) := by
  intro x hx
  have hh := (C.chord_crossing_original_mark hx).choose_spec.1
  simpa only [chordCrossingOrigin,dite_eq_left hx] using hh

theorem chordCrossingOrigin_injOn (C : DrawingPassages D) :
    Set.InjOn C.chordCrossingOrigin C.chordCrossings := by
  intro x hx y hy he
  let w : DrawingMark D := (C.chord_crossing_original_mark hx).choose
  let v : DrawingMark D := (C.chord_crossing_original_mark hy).choose
  have hwx : x ∈ C.chordCrossingsAt w := (C.chord_crossing_original_mark hx).choose_spec.2
  have hvy : y ∈ C.chordCrossingsAt v := (C.chord_crossing_original_mark hy).choose_spec.2
  have hvw : w=v := by
    apply Subtype.ext
    simpa only [chordCrossingOrigin,dite_eq_left hx,dite_eq_left hy] using he
  rw [← hvw] at hvy
  exact (C.chordCrossingsAt_subsingleton w) hwx hvy

theorem chordCrossings_finite (C : DrawingPassages D) : C.chordCrossings.Finite :=
  Set.Finite.of_injOn C.chordCrossingOrigin_mapsTo C.chordCrossingOrigin_injOn D.crossings_finite

/-- Different original crossing disks remain separately counted, even when
their two chords come from the same pair of graph edges. -/
theorem chordCrossings_ncard_le (C : DrawingPassages D) :
    C.chordCrossings.ncard ≤ finiteCrossingCount D := by
  calc
    C.chordCrossings.ncard ≤ (Paper170.crossingPoints D.toContinuousDrawing).ncard :=
      Set.ncard_le_ncard_of_injOn C.chordCrossingOrigin C.chordCrossingOrigin_mapsTo
        C.chordCrossingOrigin_injOn D.crossings_finite
    _ = finiteCrossingCount D := Set.ncard_eq_toFinset_card _ D.crossings_finite

end Paper170Geometry.DrawingPassages

end
end

end OAI
