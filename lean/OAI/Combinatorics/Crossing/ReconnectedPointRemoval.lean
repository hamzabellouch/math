import OAI.Combinatorics.Crossing.ReconnectedPaths
import OAI.Combinatorics.Crossing.ReconnectionAvoidance

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem reconnected_paths_avoid_crossing (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∉ Set.range (reconnectedForwardPath Kp Kq hm) ∧
      x ∉ Set.range (reconnectedBackwardPath Kp Kq hm) := by
  obtain ⟨hxin,havoid⟩ := C.reconnection_avoids_chord_meeting p q hpq x hxp hxq
  have hxinq : x ∈ C.crossingDisk q := by
    simpa only [DrawingPassages.crossingDisk,hm] using hxin
  constructor
  · intro hx
    rcases reconnectedForwardPath_trace Kp Kq hm hx with (hx | hx) | hx
    · exact Set.disjoint_left.mp Kp.prefix_outside hx hxin
    · exact havoid true hx
    · exact Set.disjoint_left.mp Kq.suffix_outside hx hxinq
  · intro hx
    rcases reconnectedBackwardPath_trace Kp Kq hm hx with (hx | hx) | hx
    · exact Set.disjoint_left.mp Kq.prefix_outside hx hxinq
    · exact havoid false hx
    · exact Set.disjoint_left.mp Kp.suffix_outside hx hxin

end Zarankiewicz

end

end OAI
