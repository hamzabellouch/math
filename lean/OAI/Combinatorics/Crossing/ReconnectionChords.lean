import OAI.Combinatorics.Crossing.CrossingReconnection
import OAI.Combinatorics.Crossing.CrossingDiskNeighborhood

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : AdmissibleDrawing m n}

def reconnectionStart (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) : Plane :=
  if i then C.portPoint (C.incomingPort p) else C.portPoint (C.incomingPort q)

def reconnectionEnd (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) : Plane :=
  if i then C.portPoint (C.outgoingPort q) else C.portPoint (C.outgoingPort p)

theorem reconnection_endpoints_ne (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) :
    C.reconnectionStart p q i ≠ C.reconnectionEnd p q i := by
  cases i
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort q p)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p q)

theorem crossingChord_meeting_segmentsCrossProperly (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hpq : p ≠ q) (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have he : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val=
      segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val := by
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs.trans ht.symm
  obtain ⟨hd,hsi,hti⟩ := C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property he
  exact ⟨hd,s.val,hsi,t.val,hti,he⟩

theorem reconnection_chords_disjoint (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) :
    ∀ i j : Bool, i ≠ j → Disjoint
      (segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i))
      (segment ℝ (C.reconnectionStart p q j) (C.reconnectionEnd p q j)) := by
  have hh := crossing_reconnections_disjoint _ _ _ _ hcross
  intro i j hij
  cases i <;> cases j
  · exact False.elim (hij rfl)
  · exact hh
  · exact hh.symm
  · exact False.elim (hij rfl)

theorem reconnection_endpoints_on_circle (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    squaredLength (C.reconnectionStart p q i-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.reconnectionEnd p q i-(C.innerMark p).val)=C.radius^2 := by
  cases i
  · change squaredLength (C.portPoint (C.incomingPort q)-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.portPoint (C.outgoingPort p)-(C.innerMark p).val)=C.radius^2
    exact ⟨by simpa only [hm] using C.incomingPoint_on_circle q,C.outgoingPoint_on_circle p⟩
  · change squaredLength (C.portPoint (C.incomingPort p)-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.portPoint (C.outgoingPort q)-(C.innerMark p).val)=C.radius^2
    exact ⟨C.incomingPoint_on_circle p,by simpa only [hm] using C.outgoingPoint_on_circle q⟩

theorem reconnection_open_in_disk (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    openSegmentTrace (C.reconnectionStart p q i) (C.reconnectionEnd p q i) ⊆ C.crossingDisk p := by
  rintro x ⟨t,ht,rfl⟩
  exact round_chord_in_open_disk _ _ _ _ (C.reconnection_endpoints_on_circle p q hm i).1
    (C.reconnection_endpoints_on_circle p q hm i).2 (C.reconnection_endpoints_ne p q i) t ht

end Zarankiewicz.DrawingPassages

end

end OAI
