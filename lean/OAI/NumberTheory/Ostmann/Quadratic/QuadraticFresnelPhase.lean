import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFresnelCoefficient

namespace OAI

/-! # The principal square root on the two imaginary half-axes -/

namespace Ostmann

 theorem quadratic_half_negative_imaginary {r : ℝ} (hr : 0 < r) :
    (-(r : ℂ) * Complex.I) ^ (1 / 2 : ℂ) =
      (Real.sqrt (r / 2) : ℂ) * (1 - Complex.I) := by
  have hn : ‖-(r : ℂ) * Complex.I‖ = r := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_I, mul_one]
  have hi : (-(r : ℂ) * Complex.I).im < 0 := by simpa using neg_neg_of_pos hr
  rw [one_div (2 : ℂ)]
  apply Complex.ext
  · rw [Complex.cpow_inv_two_re, hn]
    simp
  · rw [Complex.cpow_inv_two_im_eq_neg_sqrt hi, hn]
    simp

 theorem quadratic_half_positive_imaginary {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) * Complex.I) ^ (1 / 2 : ℂ) =
      (Real.sqrt (r / 2) : ℂ) * (1 + Complex.I) := by
  have hn : ‖(r : ℂ) * Complex.I‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_I, mul_one]
  have hi : 0 ≤ ((r : ℂ) * Complex.I).im := by simpa using hr.le
  rw [one_div (2 : ℂ)]
  apply Complex.ext
  · rw [Complex.cpow_inv_two_re, hn]
    simp
  · rw [Complex.cpow_inv_two_im_eq_sqrt hi, hn]
    simp

end Ostmann

end OAI
