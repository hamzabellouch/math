import OAI.Combinatorics.EditApproximation.Geometry.Parameters

namespace OAI

/-! The prescribed small parameters satisfy the group and online error inequalities. -/

namespace EditApproximation

theorem group_online_range_small {ell : ℚ} (hell : 8 ≤ ell) :
    8 * (128 * ell) * (1 / ell ^ 40) ≤ 1 / ell ^ 10 := by
  have he : 1 ≤ ell := by linarith only [hell]
  have he0 : 0 < ell := by linarith only [hell]
  have hcoef : (1024 : ℚ) ≤ ell ^ 29 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 8) hell 4
    norm_num at h
    exact (by norm_num : (1024 : ℚ) ≤ 4096) |>.trans
      (h.trans (pow_le_pow_right₀ he (by decide : 4 ≤ 29)))
  rw [mul_one_div]
  apply (div_le_div_iff₀ (pow_pos he0 40) (pow_pos he0 10)).2
  have h := mul_le_mul_of_nonneg_right hcoef (pow_nonneg he0.le 11)
  convert h using 1 <;> ring

theorem group_online_eta_range {ell : ℚ} (hell : 3 ≤ ell) :
    ell ^ 5 * (3 * (1 / ell ^ 10)) ≤ 1 / ell ^ 4 := by
  have he0 : 0 < ell := by linarith only [hell]
  have h := mul_le_mul_of_nonneg_right hell (pow_nonneg he0.le 9)
  have hmul : ell ^ 5 * (3 * (1 / ell ^ 10)) = 3 * ell ^ 5 / ell ^ 10 := by ring
  rw [hmul]
  apply (div_le_div_iff₀ (pow_pos he0 10) (pow_pos he0 4)).2
  convert h using 1 <;> ring

theorem group_rounded_error_small {ell : ℚ} (hell : 8 ≤ ell) :
    2 * (1 / ell ^ 20) + 512 * (128 * ell) * ell * (1 / ell ^ 40) ≤
      (1 / ell ^ 4) * (1 / ell ^ 10) := by
  have he : 1 ≤ ell := by linarith only [hell]
  have he0 : 0 < ell := by linarith only [hell]
  have hcoef1 : (4 : ℚ) ≤ ell ^ 6 := by
    exact (by norm_num : (4 : ℚ) ≤ 8).trans
      (hell.trans (by simpa only [pow_one] using pow_le_pow_right₀ he (by decide : 1 ≤ 6)))
  have hcoef2 : (131072 : ℚ) ≤ ell ^ 24 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 8) hell 6
    norm_num at h
    exact (by norm_num : (131072 : ℚ) ≤ 262144) |>.trans
      (h.trans (pow_le_pow_right₀ he (by decide : 6 ≤ 24)))
  have hfirst : 2 / ell ^ 20 ≤ 1 / (2 * ell ^ 14) := by
    apply (div_le_div_iff₀ (pow_pos he0 20) (by positivity : 0 < 2 * ell ^ 14)).2
    have h := mul_le_mul_of_nonneg_right hcoef1 (pow_nonneg he0.le 14)
    convert h using 1 <;> ring
  have hsecond : 65536 * ell ^ 2 / ell ^ 40 ≤ 1 / (2 * ell ^ 14) := by
    apply (div_le_div_iff₀ (pow_pos he0 40) (by positivity : 0 < 2 * ell ^ 14)).2
    have h := mul_le_mul_of_nonneg_right hcoef2 (pow_nonneg he0.le 16)
    convert h using 1 <;> ring
  have hid : (1 / ell ^ 4) * (1 / ell ^ 10) = 2 * (1 / (2 * ell ^ 14)) := by
    field_simp
  rw [hid]
  have hid2 : 512 * (128 * ell) * ell * (1 / ell ^ 40) = 65536 * ell ^ 2 / ell ^ 40 := by ring
  rw [hid2]
  have hid1 : 2 * (1 / ell ^ 20) = 2 / ell ^ 20 := by ring
  rw [hid1]
  simpa only [two_mul] using add_le_add hfirst hsecond

end EditApproximation

end OAI
