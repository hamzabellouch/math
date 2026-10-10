import OAI.Geometry.RCD.Transport.MidpointSupportVolume

namespace OAI

/-! # Both endpoint masses in the midpoint estimate -/

open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

/-- Keeping the smaller endpoint mass preserves the factor two needed
for the isodiametric argument with reflected sets. -/
theorem midpoint_root_bound_to_min_mass {n : ℕ} (hn : 0 < n)
    {a b c d : ℝ≥0∞}
    (h : c*(a^(1/(n:ℝ))+b^(1/(n:ℝ))) ≤ d^(1/(n:ℝ))) :
    (2*c)^n*min a b ≤ d := by
  have hq : 0 ≤ 1/(n:ℝ) := by positivity
  have ha := ENNReal.rpow_le_rpow (min_le_left a b) hq
  have hb := ENNReal.rpow_le_rpow (min_le_right a b) hq
  have hs : (2:ℝ≥0∞)*(min a b)^(1/(n:ℝ)) ≤ a^(1/(n:ℝ))+b^(1/(n:ℝ)) := by
    rw [two_mul]
    exact add_le_add ha hb
  have hp : (2*c)*(min a b)^(1/(n:ℝ)) ≤ d^(1/(n:ℝ)) := by
    calc
      _ = c*(2*(min a b)^(1/(n:ℝ))) := by ac_rfl
      _ ≤ _ := (mul_le_mul' le_rfl hs).trans h
  have he (x : ℝ≥0∞) : (x^(1/(n:ℝ)))^n=x := by
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul,
      one_div_mul_cancel (by exact_mod_cast hn.ne' : (n:ℝ)≠0),ENNReal.rpow_one]
  simpa only [mul_pow,he] using pow_le_pow_left' hp n

end RegularPointCoordinates

end

end OAI
