import OAI.Analysis.LipschitzHilbert.Estimates.SlopeBoxMask

namespace OAI

/-! The source sinc mask is exponentially small outside the prescribed
polynomial enlargement of its top. The estimate includes points on either
coordinate axis and uses the actual even exponent `2 * ceil L`. -/

noncomputable section
namespace LipschitzHilbert

theorem abs_sinc_le_reciprocal_of_large {L x : ℝ} (hL : 0 < L)
    (hx : L ≤ |x|) : |Real.sinc x| ≤ 1/L := by
  have hx0 : x ≠ 0 := abs_pos.mp (hL.trans_le hx)
  rw [Real.sinc_of_ne_zero hx0,abs_div]
  calc
    _ ≤ 1/|x| := div_le_div_of_nonneg_right (Real.abs_sin_le_one x) (abs_nonneg x)
    _ ≤ 1/L := one_div_le_one_div_of_le hL hx

theorem sincProductMask_tail {L x y : ℝ} (hL : 1 ≤ L)
    (hlarge : L ≤ |x| ∨ L ≤ |y|) :
    |sincProductMask ⌈L⌉₊ x y| ≤ Real.exp (-L*Real.log L) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hproduct : |Real.sinc x*Real.sinc y| ≤ 1/L := by
    rw [abs_mul]
    rcases hlarge with hx | hy
    · have hb := mul_le_mul (abs_sinc_le_reciprocal_of_large hL0 hx)
        (Real.abs_sinc_le_one y) (abs_nonneg _) (by positivity : 0 ≤ 1/L)
      simpa only [mul_one] using hb
    · have hb := mul_le_mul (Real.abs_sinc_le_one x)
        (abs_sinc_le_reciprocal_of_large hL0 hy) (abs_nonneg _) zero_le_one
      simpa only [one_mul] using hb
  have hpow := pow_le_pow_left₀ (abs_nonneg _) hproduct (2*⌈L⌉₊)
  have hexponent : L ≤ ((2*⌈L⌉₊:ℕ):ℝ) := by
    have hc := Nat.le_ceil L
    have hn : (0:ℝ) ≤ (⌈L⌉₊:ℝ) := Nat.cast_nonneg _
    push_cast
    linarith
  calc
    _ ≤ (1/L)^(2*⌈L⌉₊) := by simpa only [sincProductMask,abs_pow] using hpow
    _ = (1/L)^((2*⌈L⌉₊:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (1/L)^L := Real.rpow_le_rpow_of_exponent_ge (by positivity)
      ((div_le_one hL0).mpr hL) hexponent
    _ = Real.exp (-L*Real.log L) := by
      rw [Real.rpow_def_of_pos (by positivity : 0 < 1/L),Real.log_div one_ne_zero hL0.ne',
        Real.log_one]
      congr 1
      ring

theorem topSincMask_tail {L A x y : ℝ} (hL : 2 ≤ L)
    (hlarge : L^(A+2) ≤ |x|+|y|) :
    |topSincMask L A x y| ≤ Real.exp (-L*Real.log L) := by
  have hL0 : 0 < L := by linarith
  have hscale : 0 < L^A := Real.rpow_pos_of_pos hL0 _
  have hthreshold : 2*(L*L^A) ≤ L^(A+2) := by
    rw [Real.rpow_add hL0,Real.rpow_two]
    have hm := mul_le_mul_of_nonneg_left hL hL0.le
    have hp := mul_le_mul_of_nonneg_right hm hscale.le
    nlinarith
  have hcoordinate : L*L^A ≤ |x| ∨ L*L^A ≤ |y| := by
    by_contra hnone
    push Not at hnone
    linarith
  have hscaled : L ≤ |x/L^A| ∨ L ≤ |y/L^A| := by
    simp only [abs_div,abs_of_pos hscale]
    rcases hcoordinate with hx | hy
    · exact Or.inl ((le_div_iff₀ hscale).mpr hx)
    · exact Or.inr ((le_div_iff₀ hscale).mpr hy)
  exact sincProductMask_tail (by linarith) hscaled

theorem SlopeBox.mask_tail (T : SlopeBox) {L A : ℝ} (hL : 2 ≤ L)
    (z : ℝ × ℝ) (hlarge : L^(A+2) ≤ T.radius z) :
    |T.mask L A z| ≤ Real.exp (-L*Real.log L) :=
  topSincMask_tail hL hlarge

end LipschitzHilbert

end

end OAI
