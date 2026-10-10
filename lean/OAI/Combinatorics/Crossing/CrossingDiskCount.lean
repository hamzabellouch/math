import OAI.Combinatorics.Crossing.CrossingDiskUniqueness
import Mathlib.Data.Set.Card

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
open scoped Classical
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

def chordCrossingOrigin (C : DrawingPassages D) (x : Plane) : Plane :=
  if hx : x ∈ C.chordCrossings then (C.chord_crossing_original_mark hx).choose.val else 0

theorem chordCrossingOrigin_mapsTo (C : DrawingPassages D) :
    Set.MapsTo C.chordCrossingOrigin C.chordCrossings (crossingPoints D.toContinuousDrawing) := by
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

theorem chordCrossings_ncard_le (C : DrawingPassages D) :
    C.chordCrossings.ncard ≤ finiteCrossingCount D := by
  calc
    C.chordCrossings.ncard ≤ (crossingPoints D.toContinuousDrawing).ncard :=
      Set.ncard_le_ncard_of_injOn C.chordCrossingOrigin C.chordCrossingOrigin_mapsTo
        C.chordCrossingOrigin_injOn D.crossings_finite
    _ = finiteCrossingCount D := Set.ncard_eq_toFinset_card _ D.crossings_finite

end Zarankiewicz.DrawingPassages

end

end OAI
