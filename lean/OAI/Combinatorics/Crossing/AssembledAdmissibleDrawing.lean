import OAI.Combinatorics.Crossing.CrossingDiskNeighborhood
import OAI.Combinatorics.Crossing.ProperSegmentCrossing
import OAI.Combinatorics.Crossing.ProperCrossingLocality

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

theorem crossingChord_meeting_proper (C : DrawingPassages D) (p q : C.InnerIndex)
    (hpq : p ≠ q) (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ C.crossingDisk p ∧
      ProperCrossing
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
  · apply properCrossing_openSegments _ _ _ _ x hd
    · exact ⟨s.val,hsi,by simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs⟩
    · exact ⟨t.val,hti,by simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht⟩

end DrawingPassages
namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem assembled_crossings_proper (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : BipartiteEdge m n) (hef : e ≠ f) (x : Plane)
    (hx : x ∈ edgeInterior (E.assembledDrawing v hvinj hv) e)
    (hy : x ∈ edgeInterior (E.assembledDrawing v hvinj hv) f) :
    ProperCrossing (edgeInterior (E.assembledDrawing v hvinj hv) e)
      (edgeInterior (E.assembledDrawing v hvinj hv) f) x := by
  obtain ⟨s,hs,he⟩ := hx
  obtain ⟨t,ht,hf⟩ := hy
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)) ⟨s,he⟩ ⟨t,hf⟩
  have hpq : p ≠ q := fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨hxin,hproper⟩ := C.crossingChord_meeting_proper p q hpq x hxp hxq
  apply properCrossing_of_local_eq _ _ _ _ x hproper (C.crossingDisk p) (C.crossingDisk_isOpen p) hxin
  · intro z hz
    simpa only [hp] using (E.assembled_trace_in_crossingDisk v hvinj hv p z hz).symm
  · intro z hz
    have hzq : z ∈ C.crossingDisk q := by
      change squaredLength (z-(C.innerMark q).val) < C.radius^2
      rw [← hm]
      exact hz
    simpa only [hq] using (E.assembled_trace_in_crossingDisk v hvinj hv q z hzq).symm

def assembledAdmissible (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) : AdmissibleDrawing m n where
  toContinuousDrawing := E.assembledDrawing v hvinj hv
  crossings_finite := E.assembled_crossings_finite v hvinj hv hdet
  crossings_proper := E.assembled_crossings_proper v hvinj hv hdet
  no_triples := E.assembled_no_triples v hvinj hv hdet

theorem assembled_crossingCount_le (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    crossingCount (E.assembledAdmissible v hvinj hv hdet) ≤ finiteCrossingCount D := by
  have h := Set.ncard_le_ncard (E.assembled_crossings_subset v hvinj hv hdet) C.chordCrossings_finite
  have hcount : crossingCount (E.assembledAdmissible v hvinj hv hdet)=
      (crossingPoints (E.assembledDrawing v hvinj hv)).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (E.assembled_crossings_finite v hvinj hv hdet)]
    rfl
  rw [hcount]
  exact h.trans C.chordCrossings_ncard_le

end PolygonalExterior
end Zarankiewicz

end

end OAI
