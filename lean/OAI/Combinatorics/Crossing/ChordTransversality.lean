import OAI.Combinatorics.Crossing.CircleChords
import OAI.Combinatorics.Crossing.SegmentContinuity

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem segmentPairTransverse_of_noncollinear_endpoints (a b c d : Plane)
    (ha : orient2 c d a ≠ 0) (hb : orient2 c d b ≠ 0)
    (hc : orient2 a b c ≠ 0) (hd : orient2 a b d ≠ 0) :
    SegmentPairTransverse a b c d := by
  intro t ht u hu he
  have hdet : det2 (b-a) (d-c) ≠ 0 := by
    intro hz
    have hdiff := orient2_difference a b c d
    have heq : orient2 a b c=orient2 a b d := by linarith
    have hh := congrArg (orient2 a b) he
    rw [orient2_self_segment,orient2_segment,← heq] at hh
    apply hc
    nlinarith
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    rw [segmentPoint_zero] at he
    exact ha (by rw [he,orient2_self_segment])
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    rw [segmentPoint_one] at he
    exact hb (by rw [he,orient2_self_segment])
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    rw [segmentPoint_zero] at he
    exact hc (by rw [← he,orient2_self_segment])
  have hu1 : u ≠ 1 := by
    intro h
    subst u
    rw [segmentPoint_one] at he
    exact hd (by rw [← he,orient2_self_segment])
  exact ⟨hdet,⟨lt_of_le_of_ne ht.1 ht0.symm,lt_of_le_of_ne ht.2 ht1⟩,
    ⟨lt_of_le_of_ne hu.1 hu0.symm,lt_of_le_of_ne hu.2 hu1⟩⟩

theorem circle_orient_ne_zero (a b c : ℝ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient2 (circlePoint a) (circlePoint b) (circlePoint c) ≠ 0 := by
  rw [circle_orient_formula]
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hab.symm))
      (sub_ne_zero.mpr hac.symm)) (sub_ne_zero.mpr hbc.symm)
  · exact mul_ne_zero (mul_ne_zero (ne_of_gt (circle_denominator_pos a))
      (ne_of_gt (circle_denominator_pos b))) (ne_of_gt (circle_denominator_pos c))

theorem circle_chords_transverse (a b c d : ℝ)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    SegmentPairTransverse (circlePoint a) (circlePoint b) (circlePoint c) (circlePoint d) := by
  exact segmentPairTransverse_of_noncollinear_endpoints _ _ _ _
    (circle_orient_ne_zero c d a hcd hac.symm had.symm)
    (circle_orient_ne_zero c d b hcd hbc.symm hbd.symm)
    (circle_orient_ne_zero a b c hab hac hbc)
    (circle_orient_ne_zero a b d hab had hbd)

end Zarankiewicz

end

end OAI
