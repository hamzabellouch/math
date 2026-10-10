import OAI.Combinatorics.Crossing.ChordPairing

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentCrossingSign_reverse_right (a b c d : Plane) :
    segmentCrossingSign a b d c = -segmentCrossingSign a b c d := by
  rw [segmentCrossingSign_swap d c a b,segmentCrossingSign_reverse_left c d a b,
    neg_neg,segmentCrossingSign_swap a b c d]

theorem chordEndpointPairing_reverse_right (a b c d : ℝ) :
    chordEndpointPairing a b d c = -chordEndpointPairing a b c d := by
  unfold chordEndpointPairing
  ring

theorem circle_chord_pairing_first_ordered (a b c d : ℝ) (hab : a<b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) =
      chordEndpointPairing a b c d := by
  rcases lt_or_gt_of_ne hcd with hcd | hdc
  · exact circle_chord_pairing_ordered a b c d hab hcd hac had hbc hbd
  · have hh := circle_chord_pairing_ordered a b d c hab hdc had hac hbd hbc
    rw [segmentCrossingSign_reverse_right, chordEndpointPairing_reverse_right] at hh
    exact neg_injective hh

theorem circle_chord_pairing (a b c d : ℝ) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) =
      (orderSign a c-orderSign a d-orderSign b c+orderSign b d)/2 := by
  change _ = chordEndpointPairing a b c d
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact circle_chord_pairing_first_ordered a b c d hab hcd hac had hbc hbd
  · have hh := circle_chord_pairing_first_ordered b a c d hba hcd hbc hbd hac had
    rw [segmentCrossingSign_reverse_left, chordEndpointPairing_reverse_left] at hh
    exact neg_injective hh

end Zarankiewicz

end

end OAI
