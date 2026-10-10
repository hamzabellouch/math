import OAI.NumberTheory.TwoPoint.Fourier.MinorArcPackingSum

namespace OAI

/-! Centered representatives preserve the rational separation on the circle. -/

namespace TwoPointCorrelations

lemma minor_arc_integer_zero (z : ℤ) : ((z : ℝ) : UnitAddCircle) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨z, by simp⟩

lemma minor_arc_centered_coe (x : ℝ) :
    ((x - (round x : ℝ) : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  rw [AddCircle.coe_sub, minor_arc_integer_zero, sub_zero]

lemma minor_arc_centered_difference (x y : ℝ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) ≤
      |(x - (round x : ℝ)) - (y - (round y : ℝ))| := by
  have h := minor_arc_circle_norm_le ((x - (round x : ℝ)) - (y - (round y : ℝ)))
  rw [AddCircle.coe_sub, minor_arc_centered_coe, minor_arc_centered_coe] at h
  simpa only [dist_eq_norm] using h

lemma minor_arc_centered_small (x : ℝ) : |x - (round x : ℝ)| ≤ 1 / 2 := by
  simpa only [UnitAddCircle.norm_eq, abs_one] using
    (AddCircle.norm_le_half_period (1 : ℝ) (by norm_num) (x := (x : UnitAddCircle)))

end TwoPointCorrelations

end OAI
