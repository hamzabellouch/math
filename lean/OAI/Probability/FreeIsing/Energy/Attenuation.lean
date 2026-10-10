import Mathlib

namespace OAI

noncomputable section

namespace Problem367

def responseAttenuation (theta z : ℝ) : ℝ :=
  (1 - Real.tanh z ^ 2) / (1 - theta ^ 2 * Real.tanh z ^ 2)

lemma attenuation_denominator_pos {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    0 < 1 - theta ^ 2 * Real.tanh z ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_right hθ (sq_nonneg (Real.tanh z))
  have ht := Real.tanh_sq_lt_one z
  nlinarith

lemma responseAttenuation_pos {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    0 < responseAttenuation theta z := by
  exact div_pos (sub_pos.mpr (Real.tanh_sq_lt_one z))
    (attenuation_denominator_pos hθ z)

lemma responseAttenuation_le_one {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    responseAttenuation theta z ≤ 1 := by
  rw [responseAttenuation, div_le_one (attenuation_denominator_pos hθ z)]
  have := mul_le_mul_of_nonneg_right hθ (sq_nonneg (Real.tanh z))
  nlinarith

@[simp] lemma responseAttenuation_zero (theta : ℝ) :
    responseAttenuation theta 0 = 1 := by
  simp [responseAttenuation]

@[simp] lemma responseAttenuation_neg (theta z : ℝ) :
    responseAttenuation theta (-z) = responseAttenuation theta z := by
  simp [responseAttenuation]

lemma hasDerivAt_tanh_response (z : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh z ^ 2) z := by
  have hd := (Real.hasDerivAt_sinh z).div (Real.hasDerivAt_cosh z)
    (ne_of_gt (Real.cosh_pos z))
  convert! hd using 1
  · ext x
    exact Real.tanh_eq_sinh_div_cosh x
  · rw [Real.tanh_eq_sinh_div_cosh]
    field_simp

lemma hasDerivAt_log_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    HasDerivAt (fun x => Real.log (responseAttenuation theta x))
      (-2 * (1 - theta ^ 2) * Real.tanh z /
        (1 - theta ^ 2 * Real.tanh z ^ 2)) z := by
  have ht := hasDerivAt_tanh_response z
  have hn := (ht.pow 2).const_sub 1
  have hd := ((ht.pow 2).const_mul (theta ^ 2)).const_sub 1
  have hden := ne_of_gt (attenuation_denominator_pos hθ z)
  have hnum := ne_of_gt (sub_pos.mpr (Real.tanh_sq_lt_one z))
  have hh := (hn.div hd hden).log (ne_of_gt (responseAttenuation_pos hθ z))
  convert! hh using 1
  dsimp [responseAttenuation]
  field_simp
  ring

lemma abs_deriv_log_responseAttenuation_le {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    |deriv (fun x => Real.log (responseAttenuation theta x)) z| ≤ 2 * |Real.tanh z| := by
  rw [(hasDerivAt_log_responseAttenuation hθ z).deriv]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (attenuation_denominator_pos hθ z),
    abs_of_nonneg (sub_nonneg.mpr hθ)]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_le_iff₀ (attenuation_denominator_pos hθ z)]
  have hp := mul_le_mul_of_nonneg_left (le_of_lt (Real.tanh_sq_lt_one z)) (sq_nonneg theta)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (Real.tanh z))
  nlinarith

lemma abs_deriv_log_responseAttenuation_le_two {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    |deriv (fun x => Real.log (responseAttenuation theta x)) z| ≤ 2 := by
  exact (abs_deriv_log_responseAttenuation_le hθ z).trans
    (by nlinarith [Real.abs_tanh_lt_one z])

@[simp] lemma deriv_log_responseAttenuation_zero {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) :
    deriv (fun x => Real.log (responseAttenuation theta x)) 0 = 0 := by
  rw [(hasDerivAt_log_responseAttenuation hθ 0).deriv]
  simp

lemma lipschitzWith_log_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    LipschitzWith 2 (fun x => Real.log (responseAttenuation theta x)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_log_responseAttenuation hθ x).differentiableAt
  · intro x
    exact_mod_cast abs_deriv_log_responseAttenuation_le_two hθ x

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

lemma abs_tanh_le_abs_response (z : ℝ) : |Real.tanh z| ≤ |z| := by
  have h := lipschitzWith_tanh_response.dist_le_mul z 0
  simpa [Real.dist_eq] using h

lemma log_responseAttenuation_small_field {theta R x y : ℝ}
    (hθ : theta ^ 2 ≤ 1) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)| ≤
      (2 * R) * |x - y| := by
  have h := (convex_Icc (-R) R).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hasDerivAt_log_responseAttenuation hθ z).differentiableAt)
    (C := 2 * R) (fun z hz => ?_) (abs_le.mp hy) (abs_le.mp hx)
  · simpa only [Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs]
    have hzR : |z| ≤ R := abs_le.mpr hz
    exact (abs_deriv_log_responseAttenuation_le hθ z).trans
      (by nlinarith [abs_tanh_le_abs_response z])

lemma log_responseAttenuation_nonpos {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    Real.log (responseAttenuation theta z) ≤ 0 := by
  exact Real.log_nonpos (le_of_lt (responseAttenuation_pos hθ z))
    (responseAttenuation_le_one hθ z)

lemma responseAttenuation_le_one_sub {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    responseAttenuation theta z ≤ 1 - (1 - theta ^ 2) * Real.tanh z ^ 2 := by
  rw [responseAttenuation, div_le_iff₀ (attenuation_denominator_pos hθ z)]
  have hp : 0 ≤ theta ^ 2 * (1 - theta ^ 2) * (Real.tanh z ^ 2) ^ 2 := by
    exact mul_nonneg (mul_nonneg (sq_nonneg theta) (sub_nonneg.mpr hθ)) (sq_nonneg _)
  nlinarith

lemma responseAttenuation_le_exp {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    responseAttenuation theta z ≤ Real.exp (-(1 - theta ^ 2) * Real.tanh z ^ 2) := by
  calc
    responseAttenuation theta z ≤ 1 - (1 - theta ^ 2) * Real.tanh z ^ 2 :=
      responseAttenuation_le_one_sub hθ z
    _ ≤ Real.exp (-(1 - theta ^ 2) * Real.tanh z ^ 2) := by
      have h := Real.add_one_le_exp (-(1 - theta ^ 2) * Real.tanh z ^ 2)
      linarith

lemma log_responseAttenuation_small_field_sq {theta R x y : ℝ}
    (hθ : theta ^ 2 ≤ 1) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    (Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)) ^ 2 ≤
      4 * R ^ 2 * (x - y) ^ 2 := by
  have hR : 0 ≤ R := (abs_nonneg x).trans hx
  have h := log_responseAttenuation_small_field hθ hx hy
  have hsq := (sq_le_sq₀ (abs_nonneg
    (Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)))
    (mul_nonneg (mul_nonneg (by norm_num) hR) (abs_nonneg (x - y)))).mpr h
  norm_num [mul_pow, sq_abs, mul_assoc] at hsq ⊢
  exact hsq

end Problem367

end

end OAI
