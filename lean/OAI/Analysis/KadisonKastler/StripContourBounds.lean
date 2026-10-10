import OAI.Analysis.KadisonKastler.StripSineQuotient

namespace OAI

/-! # Decay on the horizontal edges of the modular contour -/

namespace KadisonKastler

noncomputable section

theorem norm_complex_sin_lower (z : ℂ) :
    (Real.exp |z.im| - Real.exp (-|z.im|)) / 2 ≤ ‖Complex.sin z‖ := by
  have h₁ : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have h₂ : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  norm_num only [Complex.norm_ofNat]
  rcases le_total 0 z.im with hi | hi
  · rw [abs_of_nonneg hi]
    exact div_le_div_of_nonneg_right
      (by simpa only [h₁, h₂] using (norm_sub_norm_le
        (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I)))) (by norm_num)
  · rw [abs_of_nonpos hi, neg_neg]
    have h := norm_sub_norm_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
    rw [h₂, h₁, norm_sub_rev] at h
    exact div_le_div_of_nonneg_right h (by norm_num)

theorem strip_sine_exponential_lower (x t : ℝ) (ht : 1 ≤ Real.pi * |t|) :
    Real.exp (Real.pi * |t|) / 4 ≤
      ‖Complex.sin (Real.pi * ((x : ℂ) + t * Complex.I))‖ := by
  have hs := norm_complex_sin_lower (Real.pi * ((x : ℂ) + t * Complex.I))
  have he : (Real.pi * ((x : ℂ) + t * Complex.I)).im = Real.pi * t := by simp
  rw [he, abs_mul, abs_of_pos Real.pi_pos] at hs
  have hp : 2 ≤ Real.exp (Real.pi * |t|) := by
    linarith [Real.add_one_le_exp (Real.pi * |t|)]
  have hm : Real.exp (-(Real.pi * |t|)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  linarith

theorem stripSineQuotient_decay (φ : ℝ) (f : ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖f z‖ ≤ B)
    (x t : ℝ) (hx : |x| ≤ 1 / 2) (ht : 1 ≤ Real.pi * |t|) :
    ‖stripSineQuotient φ f ((x : ℂ) + t * Complex.I)‖ ≤
      8 * B * Real.exp (-(Real.pi - |φ|) * |t|) := by
  have ht0 : t ≠ 0 := by intro h; norm_num [h] at ht
  have hz0 : (x : ℂ) + t * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add] at hi
    exact ht0 hi
  have hf : ‖f ((x : ℂ) + t * Complex.I)‖ ≤ B := hb _ (by simpa using hx)
  have hf0 : ‖f 0‖ ≤ B := hb _ (by norm_num)
  have he : ‖Complex.exp (Complex.I * φ * ((x : ℂ) + t * Complex.I))‖ ≤
      Real.exp (|φ| * |t|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hr : (Complex.I * φ * ((x : ℂ) + t * Complex.I)).re = -φ * t := by simp
    rw [hr]
    calc
      -φ * t ≤ |-φ * t| := le_abs_self _
      _ = |φ| * |t| := by rw [abs_mul, abs_neg]
  have hE : 1 ≤ Real.exp (|φ| * |t|) := Real.one_le_exp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hnum : ‖Complex.exp (Complex.I * φ * ((x : ℂ) + t * Complex.I)) *
        f ((x : ℂ) + t * Complex.I) - f 0‖ ≤ 2 * B * Real.exp (|φ| * |t|) := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    calc
      _ ≤ Real.exp (|φ| * |t|) * B + B :=
        add_le_add (mul_le_mul he hf (norm_nonneg _) (Real.exp_pos _).le) hf0
      _ ≤ _ := by nlinarith
  have hden := strip_sine_exponential_lower x t ht
  have hdpos : 0 < ‖Complex.sin (Real.pi * ((x : ℂ) + t * Complex.I))‖ :=
    (div_pos (Real.exp_pos _) (by norm_num)).trans_le hden
  rw [stripSineQuotient_eq hz0, norm_div]
  apply (div_le_iff₀ hdpos).mpr
  calc
    _ ≤ 2 * B * Real.exp (|φ| * |t|) := hnum
    _ = (8 * B * Real.exp (-(Real.pi - |φ|) * |t|)) *
        (Real.exp (Real.pi * |t|) / 4) := by
      rw [div_eq_mul_inv]
      have heq : Real.exp (-(Real.pi - |φ|) * |t|) * Real.exp (Real.pi * |t|) =
          Real.exp (|φ| * |t|) := by rw [← Real.exp_add]; congr 1; ring
      nlinarith [heq]
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

end

end KadisonKastler

end OAI
