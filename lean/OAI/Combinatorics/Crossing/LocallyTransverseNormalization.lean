import OAI.Combinatorics.Crossing.NoAdjacentLocalNormalization

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def LocallyTransverseCrossings (D : AdmissibleDrawing m n) : Prop :=
  ∀ e f : BipartiteEdge m n, e ≠ f → ∀ x,
    x ∈ edgeInterior D.toContinuousDrawing e → x ∈ edgeInterior D.toContinuousDrawing f →
      ∃ a b c d : Plane, det2 (b-a) (d-c) ≠ 0 ∧
        x ∈ openSegmentTrace a b ∧ x ∈ openSegmentTrace c d ∧
        ∃ U : Set Plane, IsOpen U ∧ x ∈ U ∧
          (∀ z ∈ U, z ∈ edgeInterior D.toContinuousDrawing e ↔ z ∈ openSegmentTrace a b) ∧
          (∀ z ∈ U, z ∈ edgeInterior D.toContinuousDrawing f ↔ z ∈ openSegmentTrace c d)

theorem DrawingPassages.crossingChord_meeting_det {D : FiniteIntersectionDrawing m n}
    (C : DrawingPassages D) (p q : C.InnerIndex) (hpq : p ≠ q)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    det2 (C.portPoint (C.outgoingPort p)-C.portPoint (C.incomingPort p))
      (C.portPoint (C.outgoingPort q)-C.portPoint (C.incomingPort q)) ≠ 0 := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have he : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val =
      segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val := by
    simpa only [DrawingPassages.crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]
      using hs.trans ht.symm
  exact (C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property he).1

theorem PolygonalExterior.assembled_locallyTransverseCrossings
    {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D} (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    LocallyTransverseCrossings (E.assembledAdmissible v hvinj hv hdet) := by
  intro e f hef x hx hy
  let A := E.assembledAdmissible v hvinj hv hdet
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (edgeInterior_not_vertex A.toContinuousDrawing e x hx)
    (edgeInterior_subset_range A.toContinuousDrawing e hx)
    (edgeInterior_subset_range A.toContinuousDrawing f hy)
  have hpq : p ≠ q := fun h => hef (hp.symm.trans ((congrArg Sigma.fst h).trans hq))
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hxin := (C.crossingChord_meeting_proper p q hpq x hxp hxq).1
  have hxqin := (C.crossingChord_meeting_proper q p (Ne.symm hpq) x hxq hxp).1
  refine ⟨C.portPoint (C.incomingPort p),C.portPoint (C.outgoingPort p),
    C.portPoint (C.incomingPort q),C.portPoint (C.outgoingPort q),
    C.crossingChord_meeting_det p q hpq x hxp hxq,
    (C.crossingChord_openTrace_iff p x hxin).mp hxp,
    (C.crossingChord_openTrace_iff q x hxqin).mp hxq,
    C.crossingDisk p,C.crossingDisk_isOpen p,hxin,?_,?_⟩
  · intro z hz
    change z ∈ edgeInterior (E.assembledDrawing v hvinj hv) e ↔ _
    simpa only [hp] using E.assembled_trace_in_crossingDisk v hvinj hv p z hz
  · intro z hz
    have hzq : z ∈ C.crossingDisk q := by
      change squaredLength (z-(C.innerMark q).val) < C.radius^2
      rw [← hm]
      exact hz
    change z ∈ edgeInterior (E.assembledDrawing v hvinj hv) f ↔ _
    simpa only [hq] using E.assembled_trace_in_crossingDisk v hvinj hv q z hzq

theorem polygonal_no_adjacent_locally_transverse (D : AdmissibleDrawing m n) :
    ∃ A : AdmissibleDrawing m n, crossingCount A ≤ crossingCount D ∧
      (∀ e, HasFiniteAffineCover (A.edge e)) ∧ NoAdjacentCrossings A ∧
      LocallyStraightCrossings A ∧ LocallyTransverseCrossings A := by
  obtain ⟨B,C,E,v,hvinj,hv,hdet,hnorm,hcount⟩ := exists_no_adjacent_assembled D
  exact ⟨E.assembledAdmissible v hvinj hv hdet,hcount,E.assembledEdge_hasFiniteAffineCover v,
    hnorm,E.assembled_locallyStraightCrossings v hvinj hv hdet,
    E.assembled_locallyTransverseCrossings v hvinj hv hdet⟩

end Zarankiewicz

end

end OAI
