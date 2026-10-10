import OAI.Combinatorics.CompleteCrossing.Assembly
import OAI.Combinatorics.Crossing.PolygonalNormalization
import OAI.Combinatorics.Crossing.ProperCrossingLocality
import OAI.Combinatorics.Crossing.ProperSegmentCrossing

namespace OAI

/-! Admissible polygonal replacement and retention of crossing counts. -/

section

/-! Inside a crossing disk, an assembled edge has exactly its assigned straight chord trace. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

def crossingDisk (C : DrawingPassages D) (p : C.InnerIndex) : Set Plane :=
  {x | squaredLength (x-(C.innerMark p).val) < C.radius^2}

theorem crossingDisk_isOpen (C : DrawingPassages D) (p : C.InnerIndex) : IsOpen (C.crossingDisk p) := by
  apply isOpen_lt _ continuous_const
  unfold squaredLength
  fun_prop

theorem crossingDisk_subset_closed (C : DrawingPassages D) (p : C.InnerIndex) :
    C.crossingDisk p ⊆ closedRoundDisk (C.innerMark p).val C.radius := by
  intro x hx
  exact (show squaredLength (x-(C.innerMark p).val) < C.radius^2 from hx).le

theorem crossingDisk_disjoint_vertex_disk (C : DrawingPassages D) (p : C.InnerIndex)
    (j : Vertex) :
    Disjoint (C.crossingDisk p) (closedRoundDisk (D.vertex j) C.radius) := by
  have hn : C.innerMark p ≠ C.vertexMark j := by
    intro he
    exact crossing_not_vertex D (C.innerMark p).val (C.innerMark_is_crossing p) j (congrArg Subtype.val he)
  exact (C.disks_disjoint _ _ hn).mono (C.crossingDisk_subset_closed p) Set.Subset.rfl

theorem crossingChord_openTrace_iff (C : DrawingPassages D) (p : C.InnerIndex)
    (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Set.range (C.crossingChord p) ↔
      x ∈ openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) := by
  constructor
  · rintro ⟨t,ht⟩
    have ht0 : t ≠ 0 := by
      intro he
      subst t
      rw [Path.source] at ht
      change squaredLength (x-(C.innerMark p).val) < C.radius^2 at hx
      rw [← ht,C.incomingPoint_on_circle] at hx
      exact lt_irrefl _ hx
    have ht1 : t ≠ 1 := by
      intro he
      subst t
      rw [Path.target] at ht
      change squaredLength (x-(C.innerMark p).val) < C.radius^2 at hx
      rw [← ht,C.outgoingPoint_on_circle] at hx
      exact lt_irrefl _ hx
    refine ⟨t.val,⟨?_,?_⟩,?_⟩
    · exact lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm))
    · exact lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))
    · simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  · rintro ⟨t,ht,he⟩
    refine ⟨⟨t,ht.1.le,ht.2.le⟩,?_⟩
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he

end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_range_in_crossingDisk (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Set.range (E.assembledEdge v p.1) ↔ x ∈ Set.range (C.crossingChord p) := by
  constructor
  · intro he
    rcases (E.assembledEdge_range_iff v p.1 x).mp he with (he | ⟨i,hi,he⟩ | ⟨q,hq,he⟩) | he
    · exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
        hx (C.vertex_spoke_range_in_disk v hv _ (C.startPortAt p.1) he))
    · obtain ⟨t,rfl⟩ := he
      exact False.elim (hx.not_ge (E.outside_open_disks i t (C.innerMark p)))
    · have hm : C.innerMark q=C.innerMark p := by
        by_contra hn
        exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
          (C.crossingChord_range_subset_disk q he) (C.crossingDisk_subset_closed p hx)
      have hqp := C.innerIndex_eq_of_edge_mark q p hq hm
      exact hqp ▸ he
    · rw [endSpoke_range] at he
      exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
        hx (C.vertex_spoke_range_in_disk v hv _ (C.endPortAt p.1) he))
  · intro he
    apply (E.assembledEdge_range_iff v p.1 x).mpr
    exact Or.inl (Or.inr (Or.inr ⟨p,rfl,he⟩))

theorem assembled_trace_in_crossingDisk (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) p.1 ↔
      x ∈ openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) := by
  have havoid : ∀ j, x ≠ v j := by
    intro j he
    exact Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p j) hx (he.symm ▸ (hv j).le)
  rw [← C.crossingChord_openTrace_iff p x hx,← E.assembled_range_in_crossingDisk v hv p x hx]
  constructor
  · rintro ⟨t,ht,he⟩
    exact ⟨t,he⟩
  · rintro ⟨t,he⟩
    have ht0 : t ≠ 0 := by
      intro ht
      subst t
      rw [Path.source] at he
      exact havoid _ he.symm
    have ht1 : t ≠ 1 := by
      intro ht
      subst t
      rw [Path.target] at he
      exact havoid _ he.symm
    exact ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,he⟩

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! All admissibility conditions and spatial crossing-count nonincrease for the assembled drawing. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}

theorem crossingChord_meeting_proper (C : DrawingPassages D) (p q : C.InnerIndex)
    (hpq : p ≠ q) (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ C.crossingDisk p ∧
      Paper170.ProperCrossing
        (openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)))
        (openSegmentTrace (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) x := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have hst : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val =
      segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val := by
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs.trans ht.symm
  obtain ⟨hd,hsi,hti⟩ := C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property hst
  refine ⟨?_,?_⟩
  · rw [← hs]
    exact C.crossingChord_interior_in_disk p s hsi
  · constructor
    apply properCrossing_openSegments _ _ _ _ x hd
    · exact ⟨s.val,hsi,by simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs⟩
    · exact ⟨t.val,hti,by simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht⟩

end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_crossings_proper (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : Edge) (hef : e ≠ f) (x : Plane)
    (hx : x ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e)
    (hy : x ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f) :
    Paper170.ProperCrossing (Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e)
      (Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f) x := by
  obtain ⟨s,hs,he⟩ := hx
  obtain ⟨t,ht,hf⟩ := hy
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)) ⟨s,he⟩ ⟨t,hf⟩
  have hpq : p ≠ q := fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨hxin,hproper⟩ := C.crossingChord_meeting_proper p q hpq x hxp hxq
  constructor
  apply properCrossing_of_local_eq _ _ _ _ x hproper.chart_exists (C.crossingDisk p) (C.crossingDisk_isOpen p) hxin
  · intro z hz
    simpa only [hp] using (E.assembled_trace_in_crossingDisk v hvinj hv p z hz).symm
  · intro z hz
    have hzq : z ∈ C.crossingDisk q := by
      change squaredLength (z-(C.innerMark q).val) < C.radius^2
      rw [← hm]
      exact hz
    simpa only [hq] using (E.assembled_trace_in_crossingDisk v hvinj hv q z hzq).symm

def assembledAdmissible (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) : Paper170.AdmissibleDrawing graph where
  toContinuousDrawing := E.assembledDrawing v hvinj hv
  crossings_finite := E.assembled_crossings_finite v hvinj hv hdet
  crossings_proper := E.assembled_crossings_proper v hvinj hv hdet
  no_triples := E.assembled_no_triples v hvinj hv hdet

theorem assembled_crossingCount_le (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) ≤ finiteCrossingCount D := by
  have h := Set.ncard_le_ncard (E.assembled_crossings_subset v hvinj hv hdet) C.chordCrossings_finite
  have hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet)=
      (Paper170.crossingPoints (E.assembledDrawing v hvinj hv)).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (E.assembled_crossings_finite v hvinj hv hdet)]
    rfl
  rw [hcount]
  exact h.trans C.chordCrossings_ncard_le

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Appendix A's actual polygonal normalization, with full admissibility and point-count control. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry

namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem middlePath_hasFiniteAffineCover (E : PolygonalExterior C) (e : Edge) :
    HasFiniteAffineCover (E.middlePath e) :=
  alternatingPath_hasFiniteAffineCover _ _ _ _ (fun i => (E.chain (C.orderedArc e i)).hasFiniteAffineCover)
    (fun _ => hasFiniteAffineCover_segment _ _) _

theorem assembledEdge_hasFiniteAffineCover (E : PolygonalExterior C)
    (v : Vertex → Plane) (e : Edge) :
    HasFiniteAffineCover (E.assembledEdge v e) := by
  apply HasFiniteAffineCover.trans
  · apply HasFiniteAffineCover.trans (hasFiniteAffineCover_segment _ _)
    exact E.middlePath_hasFiniteAffineCover e
  · simp only [endSpoke,Path.segment_symm]
    exact hasFiniteAffineCover_segment _ _

end PolygonalExterior

/-- Finite contacts and no triples suffice to construct genuinely proper crossings. -/
theorem finite_intersection_normalization [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) :
    ∃ D' : Paper170.AdmissibleDrawing graph,
      (∀ e, HasFiniteAffineCover (D'.edge e)) ∧ Paper170.crossingCount D' ≤ finiteCrossingCount D := by
  obtain ⟨C⟩ := nonempty_drawingPassages D
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  exact ⟨E.assembledAdmissible v hvinj hv hdet,E.assembledEdge_hasFiniteAffineCover v,
    E.assembled_crossingCount_le v hvinj hv hdet⟩

/-- An arbitrary admissible continuous drawing admits an actual admissible
polygonal drawing with no more spatial crossing points. Vertices and routes
are allowed to move. No one-crossing-per-pair or adjacency condition is assumed. -/
theorem polygonal_normalization [Fintype Vertex] [Fintype Edge] (D : Paper170.AdmissibleDrawing graph) :
    ∃ D' : Paper170.AdmissibleDrawing graph,
      (∀ e, HasFiniteAffineCover (D'.edge e)) ∧ Paper170.crossingCount D' ≤ Paper170.crossingCount D := by
  obtain ⟨C⟩ := nonempty_drawingPassages D.toFiniteIntersectionDrawing
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  exact ⟨E.assembledAdmissible v hvinj hv hdet,E.assembledEdge_hasFiniteAffineCover v,
    E.assembled_crossingCount_le v hvinj hv hdet⟩

end Paper170Geometry

end
end

section

/-! At equal total count, reassembly retains every original crossing and its incident pair. -/
noncomputable section
open Set
namespace Paper170Geometry
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace DrawingPassages
variable {D : FiniteIntersectionDrawing graph}

theorem chordCrossingOrigin_eq_innerMark (C : DrawingPassages D) {y : Plane}
    (hy : y ∈ C.chordCrossings) (p : C.InnerIndex) (hp : y ∈ Set.range (C.crossingChord p)) :
    C.chordCrossingOrigin y = (C.innerMark p).val := by
  unfold chordCrossingOrigin
  rw [dite_eq_left hy]
  obtain ⟨r,s,hrs,hr,hs,hyr,hys⟩ := (C.chord_crossing_original_mark hy).choose_spec.2
  exact congrArg Subtype.val ((C.chord_meeting_marks_eq p r hp hyr).trans hr).symm

end DrawingPassages
namespace PolygonalExterior
variable {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}

theorem assembled_origin_mem_pair (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : Edge) (hef : e ≠ f) (y : Plane)
    (he : y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e)
    (hf : y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f) :
    C.chordCrossingOrigin y ∈ Paper170.edgeInterior D.toContinuousDrawing e ∧
      C.chordCrossingOrigin y ∈ Paper170.edgeInterior D.toContinuousDrawing f := by
  have hy := E.assembled_crossings_subset v hvinj hv hdet ⟨e,f,hef,he,hf⟩
  obtain ⟨s,hs,hys⟩ := he
  obtain ⟨t,ht,hyt⟩ := hf
  obtain ⟨p,q,hp,hq,hyp,hyq⟩ := E.assembled_meeting_chords v hv hdet e f hef y
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (hys.trans heq))
    ⟨s,hys⟩ ⟨t,hyt⟩
  constructor
  · rw [C.chordCrossingOrigin_eq_innerMark hy p hyp, ← hp]
    exact ⟨C.node p.1 p.2.val,C.inner_parameter_interior p,rfl⟩
  · rw [C.chordCrossingOrigin_eq_innerMark hy q hyq, ← hq]
    exact ⟨C.node q.1 q.2.val,C.inner_parameter_interior q,rfl⟩

theorem assembled_origin_surj_of_count_eq (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) = finiteCrossingCount D) :
    Set.SurjOn C.chordCrossingOrigin (Paper170.crossingPoints (E.assembledDrawing v hvinj hv))
      (Paper170.crossingPoints D.toContinuousDrawing) := by
  have hsub := E.assembled_crossings_subset v hvinj hv hdet
  have hmap := C.chordCrossingOrigin_mapsTo.mono_left hsub
  have hinj := C.chordCrossingOrigin_injOn.mono hsub
  have hsize : (Paper170.crossingPoints D.toContinuousDrawing).ncard ≤
      (C.chordCrossingOrigin '' Paper170.crossingPoints (E.assembledDrawing v hvinj hv)).ncard := by
    rw [hinj.ncard_image, ← finiteCrossingCount_eq_ncard]
    rw [Set.ncard_eq_toFinset_card _ (E.assembled_crossings_finite v hvinj hv hdet)]
    exact hcount.ge
  have heq := Set.eq_of_subset_of_ncard_le hmap.image_subset hsize D.crossings_finite
  intro x hx
  rw [← heq] at hx
  exact hx

theorem assembled_pair_retained_of_count_eq
    {D₀ : Paper170.AdmissibleDrawing graph} {C₀ : DrawingPassages D₀.toFiniteIntersectionDrawing}
    (E : PolygonalExterior C₀) (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D₀.vertex j) < C₀.radius^2)
    (hdet : ∀ j (p q : C₀.PortsAt (C₀.vertexMark j)), p ≠ q →
      det2 (C₀.portPoint p.val-v j) (C₀.portPoint q.val-v j) ≠ 0)
    (hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) =
      Paper170.crossingCount D₀)
    (e f : Edge) (hef : e ≠ f) (x : Plane)
    (hxe : x ∈ Paper170.edgeInterior D₀.toContinuousDrawing e)
    (hxf : x ∈ Paper170.edgeInterior D₀.toContinuousDrawing f) :
    ∃ y, y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e ∧
      y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f := by
  obtain ⟨y,hy,hxy⟩ := E.assembled_origin_surj_of_count_eq v hvinj hv hdet hcount
    (show x ∈ Paper170.crossingPoints D₀.toContinuousDrawing from ⟨e,f,hef,hxe,hxf⟩)
  obtain ⟨a,b,hab,hya,hyb⟩ := hy
  have hold := E.assembled_origin_mem_pair v hvinj hv hdet a b hab y hya hyb
  rw [hxy] at hold
  have ha := (crossing_incident_iff D₀ x e f hef hxe hxf a).mp hold.1
  have hb := (crossing_incident_iff D₀ x e f hef hxe hxf b).mp hold.2
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (hab rfl)
  · exact ⟨y,hya,hyb⟩
  · exact ⟨y,hyb,hya⟩
  · exact False.elim (hab rfl)

end PolygonalExterior
end Paper170Geometry

end
end

section

/-! Subdivide actual polygonal drawings at all marks and any extra finite set of spatial points. -/
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}

namespace Paper170Geometry
theorem exists_drawing_subdivision_at [Fintype Vertex] (D : Paper170.AdmissibleDrawing graph)
    (hpoly : ∀ e, HasFiniteAffineCover (D.edge e)) (S : Set Plane) (hS : S.Finite) :
    ∃ P : ∀ e, PolygonalParametrization (D.edge e),
      (∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot) ∧
      (∀ e t, D.edge e t ∈ S → t ∈ Set.range (P e).knot) := by
  classical
  have hfinite (e : Edge) : ((D.edge e) ⁻¹' (drawingMarks D.toFiniteIntersectionDrawing ∪ S)).Finite :=
    ((drawingMarks_finite D.toFiniteIntersectionDrawing).union hS).preimage (D.edge_injective e).injOn
  have hex (e : Edge) := (hpoly e).refine (hfinite e).toFinset
  choose P hP using hex
  refine ⟨P,?_,?_⟩
  · intro e t ht
    exact hP e (by simpa using Or.inl ht)
  · intro e t ht
    exact hP e (by simpa using Or.inr ht)

namespace PolygonalExterior
variable {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem exists_assembled_port_subdivision [Fintype Vertex] [Fintype Edge] (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    ∃ P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e),
      (∀ e t, E.assembledEdge v e t ∈ drawingMarks (E.assembledAdmissible v hvinj hv hdet).toFiniteIntersectionDrawing →
        t ∈ Set.range (P e).knot) ∧
      (∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot) :=
  exists_drawing_subdivision_at (E.assembledAdmissible v hvinj hv hdet)
    (E.assembledEdge_hasFiniteAffineCover v) (Set.range C.portPoint) (Set.finite_range _)

end PolygonalExterior
end Paper170Geometry

end
end

end OAI
