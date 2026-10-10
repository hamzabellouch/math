import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! The actual even sinc-product mask from (src-8), including its
quadratic approximation to one and the stated logarithmic-scale error. -/

noncomputable section

namespace LipschitzHilbert

def sincProductMask (n : ℕ) (x y : ℝ) : ℝ := (Real.sinc x*Real.sinc y)^(2*n)

theorem sincProductMask_nonneg (n : ℕ) (x y : ℝ) : 0 ≤ sincProductMask n x y := by
  unfold sincProductMask
  exact Even.pow_nonneg (even_two_mul n) _

theorem sincProductMask_le_one (n : ℕ) (x y : ℝ) : sincProductMask n x y ≤ 1 := by
  have h : |Real.sinc x*Real.sinc y| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sinc_le_one x) (Real.abs_sinc_le_one y)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hp := pow_le_pow_left₀ (abs_nonneg _) h (2*n)
  exact (le_abs_self _).trans (by simpa only [sincProductMask, abs_pow, one_pow] using hp)

theorem abs_one_sub_sinc_le (x : ℝ) : |1-Real.sinc x| ≤ x^2/6 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [Real.sinc_of_ne_zero hx,
    show 1-Real.sin x/x = (x-Real.sin x)/x by field_simp, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hx)).mpr
  calc
    _ ≤ |x|^3/6 := Real.abs_sub_sin_le x
    _ = x^2/6*|x| := by rw [← sq_abs]; ring

theorem abs_one_sub_sinc_product_le (x y : ℝ) :
    |1-Real.sinc x*Real.sinc y| ≤ (x^2+y^2)/6 := by
  calc
    _ = |(1-Real.sinc x)+Real.sinc x*(1-Real.sinc y)| := by congr 1; ring
    _ ≤ |1-Real.sinc x|+|Real.sinc x*(1-Real.sinc y)| := abs_add_le _ _
    _ = |1-Real.sinc x|+|Real.sinc x| * |1-Real.sinc y| := by rw [abs_mul]
    _ ≤ x^2/6+1*(y^2/6) := add_le_add (abs_one_sub_sinc_le x)
      (mul_le_mul (Real.abs_sinc_le_one x) (abs_one_sub_sinc_le y) (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem abs_one_sub_sincProductMask (n : ℕ) (x y : ℝ) :
    |1-sincProductMask n x y| ≤ (n:ℝ)/3*(x^2+y^2) := by
  have hz : |Real.sinc x*Real.sinc y| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sinc_le_one x) (Real.abs_sinc_le_one y)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have h := abs_pow_sub_pow_le (a := (1:ℝ)) (b := Real.sinc x*Real.sinc y) (n := 2*n)
  simp only [one_pow, abs_one, max_eq_left hz, mul_one, Nat.cast_mul, Nat.cast_ofNat] at h
  have hb := mul_le_mul_of_nonneg_right (abs_one_sub_sinc_product_le x y)
    (show (0:ℝ) ≤ 2*(n:ℝ) by positivity)
  exact h.trans (by convert hb using 1; ring)

end LipschitzHilbert

end

end OAI
