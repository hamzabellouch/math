import OAI.Combinatorics.Crossing.DiskFillingContainment
import OAI.Combinatorics.Crossing.SegmentIntersectionUnique

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

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
    ∃ w : DrawingMark D, w.val ∈ crossingPoints D.toContinuousDrawing ∧ x ∈ C.chordCrossingsAt w := by
  obtain ⟨p,q,hpq,hp,hq⟩ := hx
  refine ⟨C.innerMark p,C.innerMark_is_crossing p,p,q,hpq,rfl,?_,hp,hq⟩
  exact (C.chord_meeting_marks_eq p q hp hq).symm

end Zarankiewicz.DrawingPassages

end

end OAI
