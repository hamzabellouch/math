import OAI.Combinatorics.Crossing.CircleChords

namespace OAI

namespace Zarankiewicz

theorem circlePoint_one_add_x (t : ℝ) : 1+(circlePoint t).1 = 2/(1+t^2) := by
  have h := ne_of_gt (circle_denominator_pos t)
  dsimp [circlePoint]
  field_simp
  ring

theorem circlePoint_avoids_cut (t : ℝ) : (circlePoint t).1 ≠ -1 := by
  have hh : 0 < 1+(circlePoint t).1 := by
    rw [circlePoint_one_add_x]
    exact div_pos (by norm_num) (circle_denominator_pos t)
  linarith

theorem circlePoint_surjective_away_cut (z : Plane) (hz : z.1^2+z.2^2 = 1) (hcut : z.1 ≠ -1) :
    circlePoint (z.2/(1+z.1)) = z := by
  have hx : 0 < 1+z.1 := by
    have hy := sq_nonneg z.2
    have hnonneg : 0 ≤ 1+z.1 := by nlinarith
    rcases hnonneg.eq_or_lt with he | he
    · exfalso
      apply hcut
      linarith
    · exact he
  have hxn := ne_of_gt hx
  have hden : 1+(z.2/(1+z.1))^2 = 2/(1+z.1) := by
    field_simp
    nlinarith
  apply Prod.ext
  · change (1-(z.2/(1+z.1))^2)/(1+(z.2/(1+z.1))^2) = z.1
    rw [hden]
    field_simp
    nlinarith [congrArg (fun t : ℝ => (1+z.1)*t) hz]
  · change (2*(z.2/(1+z.1)))/(1+(z.2/(1+z.1))^2) = z.2
    rw [hden]
    field_simp

end Zarankiewicz

end OAI
