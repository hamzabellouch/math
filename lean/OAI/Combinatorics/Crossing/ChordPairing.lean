import OAI.Combinatorics.Crossing.CircleChords

namespace OAI

noncomputable section
namespace Zarankiewicz

def orderSign (a b : ℝ) : ℝ := if a < b then 1 else if b < a then -1 else 0

def chordEndpointPairing (a b c d : ℝ) : ℝ :=
  (orderSign a c-orderSign a d-orderSign b c+orderSign b d)/2

theorem orderSign_swap (a b : ℝ) : orderSign b a = -orderSign a b := by
  unfold orderSign
  split_ifs <;> linarith

theorem chordEndpointPairing_reverse_left (a b c d : ℝ) :
    chordEndpointPairing b a c d = -chordEndpointPairing a b c d := by
  unfold chordEndpointPairing
  ring

theorem chordEndpointPairing_swap (a b c d : ℝ) :
    chordEndpointPairing c d a b = -chordEndpointPairing a b c d := by
  unfold chordEndpointPairing
  rw [orderSign_swap c a,orderSign_swap c b,orderSign_swap d a,orderSign_swap d b]
  ring

theorem circle_chords_separated (a b c d : ℝ) (hab : a<b) (hbc : b<c) (hcd : c<d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) = 0 := by
  have hh := not_segmentsCrossProperly_of_same_side (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d)
    (Or.inl ⟨circle_orient_pos a b c hab hbc,circle_orient_pos a b d hab (hbc.trans hcd)⟩)
  simp [segmentCrossingSign,hh]

theorem circle_chords_nested (a c d b : ℝ) (hac : a<c) (hcd : c<d) (hdb : d<b) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) = 0 := by
  have hc : orient2 (circlePoint a) (circlePoint b) (circlePoint c) < 0 := by
    rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos a c b hac (hcd.trans hdb))
  have hd : orient2 (circlePoint a) (circlePoint b) (circlePoint d) < 0 := by
    rw [orient2_swap_ends]
    exact neg_neg_of_pos (circle_orient_pos a d b (hac.trans hcd) hdb)
  have hh := not_segmentsCrossProperly_of_same_side _ _ _ _ (Or.inr ⟨hc,hd⟩)
  simp [segmentCrossingSign,hh]

theorem circle_chord_pairing_ordered (a b c d : ℝ) (hab : a<b) (hcd : c<d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    segmentCrossingSign (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) =
      chordEndpointPairing a b c d := by
  by_cases hac' : a<c
  · by_cases hbc' : b<c
    · rw [circle_chords_separated a b c d hab hbc' hcd]
      unfold chordEndpointPairing orderSign
      split_ifs <;> norm_num <;> linarith
    · have hcb : c<b := lt_of_le_of_ne (le_of_not_gt hbc') (Ne.symm hbc)
      by_cases hbd' : b<d
      · rw [circle_chords_alternating_positive a c b d hac' hcb hbd']
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith
      · have hdb : d<b := lt_of_le_of_ne (le_of_not_gt hbd') (Ne.symm hbd)
        rw [circle_chords_nested a c d b hac' hcd hdb]
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith
  · have hca : c<a := lt_of_le_of_ne (le_of_not_gt hac') (Ne.symm hac)
    by_cases hda : d<a
    · rw [segmentCrossingSign_swap, circle_chords_separated c d a b hcd hda hab]
      unfold chordEndpointPairing orderSign
      split_ifs <;> norm_num <;> linarith
    · have had' : a<d := lt_of_le_of_ne (le_of_not_gt hda) had
      by_cases hdb : d<b
      · rw [segmentCrossingSign_swap, circle_chords_alternating_positive c a d b hca had' hdb]
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith
      · have hbd' : b<d := lt_of_le_of_ne (le_of_not_gt hdb) hbd
        rw [segmentCrossingSign_swap, circle_chords_nested c a b d hca hab hbd']
        unfold chordEndpointPairing orderSign
        split_ifs <;> norm_num <;> linarith

end Zarankiewicz

end

end OAI
