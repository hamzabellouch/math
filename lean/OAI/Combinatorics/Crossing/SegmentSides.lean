import OAI.Combinatorics.Crossing.SegmentParameters

namespace OAI

noncomputable section
namespace Zarankiewicz

def orient2 (a b c : Plane) : ℝ := det2 (b-a) (c-a)

theorem orient2_self_segment (a b : Plane) (t : ℝ) : orient2 a b (segmentPoint a b t) = 0 := by
  dsimp [orient2, det2, segmentPoint]
  ring

theorem orient2_segment (a b c d : Plane) (u : ℝ) :
    orient2 a b (segmentPoint c d u) = (1-u)*orient2 a b c+u*orient2 a b d := by
  dsimp [orient2,det2,segmentPoint]
  ring

theorem orient2_difference (a b c d : Plane) :
    orient2 a b d-orient2 a b c = det2 (b-a) (d-c) := by
  dsimp [orient2,det2]
  ring

theorem orient2_other_difference (a b c d : Plane) :
    orient2 c d a-orient2 c d b = det2 (b-a) (d-c) := by
  dsimp [orient2,det2]
  ring

theorem segmentCrossingSign_of_positive_sides (a b c d : Plane)
    (hc : orient2 a b c < 0) (hd : 0 < orient2 a b d)
    (ha : 0 < orient2 c d a) (hb : orient2 c d b < 0) :
    segmentCrossingSign a b c d = 1 := by
  have hdiff := orient2_difference a b c d
  have hother := orient2_other_difference a b c d
  have hdet : 0 < det2 (b-a) (d-c) := by linarith
  have hcros : SegmentsCrossProperly a b c d := by
    apply (segmentsCrossProperly_iff_parameters a b c d (ne_of_gt hdet)).mpr
    constructor
    · change 0 < orient2 c d a / det2 (b-a) (d-c) ∧ orient2 c d a / det2 (b-a) (d-c) < 1
      exact ⟨div_pos ha hdet, (div_lt_one hdet).mpr (by linarith)⟩
    · change 0 < -orient2 a b c / det2 (b-a) (d-c) ∧ -orient2 a b c / det2 (b-a) (d-c) < 1
      exact ⟨div_pos (neg_pos.mpr hc) hdet, (div_lt_one hdet).mpr (by linarith)⟩
  simp [segmentCrossingSign,hcros,hdet]

theorem not_segmentsCrossProperly_of_same_side (a b c d : Plane)
    (hside : (0 < orient2 a b c ∧ 0 < orient2 a b d) ∨
      (orient2 a b c < 0 ∧ orient2 a b d < 0)) : ¬ SegmentsCrossProperly a b c d := by
  rintro ⟨_,t,ht,u,hu,he⟩
  have hzero := congrArg (orient2 a b) he
  rw [orient2_self_segment,orient2_segment] at hzero
  have hpos : 0 < 1-u := by linarith [hu.2]
  rcases hside with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · have := add_pos (mul_pos hpos hc) (mul_pos hu.1 hd)
    linarith
  · have := add_neg (mul_neg_of_pos_of_neg hpos hc) (mul_neg_of_pos_of_neg hu.1 hd)
    linarith

end Zarankiewicz

end

end OAI
