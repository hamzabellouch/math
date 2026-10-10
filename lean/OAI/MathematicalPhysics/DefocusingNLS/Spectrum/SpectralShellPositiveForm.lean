import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellMatchedCoupling

namespace OAI

/-! The defocusing coefficient matrix remains nonnegative after the two
Liouville phase changes. This is the interior sign used for high angular modes. -/

namespace DefocusingNLS

theorem spectralDiagonalCoefficient_real (m : ℕ) (q : ℂ) :
    spectralDiagonalCoefficient m q = (((m : ℝ)+1)*‖q‖^(2*m) : ℝ) := by
  calc
    _ = ((m+1 : ℕ) : ℂ)*(q*star q)^m := by
      rw [spectralDiagonalCoefficient,mul_pow]
      ring
    _ = ((m+1 : ℕ) : ℂ)*((‖q‖ : ℂ)^2)^m := by
      rw [Complex.star_def,Complex.mul_conj']
    _ = _ := by push_cast; rw [← pow_mul]

private theorem real_diagonal_form (d : ℝ) (u : ℂ) :
    (star u*((d : ℂ)*u)).re = d*‖u‖^2 := by
  rw [Complex.sq_norm]
  simp only [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

private theorem positive_pair (d : ℝ) (cp cm u v : ℂ)
    (hd : 0 ≤ d) (hp : ‖cp‖ ≤ d) (hm : ‖cm‖ ≤ d) :
    0 ≤ (star u*((d : ℂ)*u+cp*v)).re+(star v*((d : ℂ)*v+cm*u)).re := by
  have hpn : ‖star u*(cp*v)‖ ≤ d*‖u‖*‖v‖ := by
    rw [norm_mul,norm_star,norm_mul]
    nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg (norm_nonneg u) (norm_nonneg v))]
  have hmn : ‖star v*(cm*u)‖ ≤ d*‖u‖*‖v‖ := by
    rw [norm_mul,norm_star,norm_mul]
    nlinarith [mul_le_mul_of_nonneg_right hm (mul_nonneg (norm_nonneg u) (norm_nonneg v))]
  have hpr := (abs_le.mp (Complex.abs_re_le_norm (star u*(cp*v)))).1
  have hmr := (abs_le.mp (Complex.abs_re_le_norm (star v*(cm*u)))).1
  rw [mul_add,mul_add,Complex.add_re,Complex.add_re,real_diagonal_form,real_diagonal_form]
  nlinarith [mul_nonneg hd (sq_nonneg (‖u‖-‖v‖))]

theorem spectralShellForcing_nonnegative (m : ℕ) (hm : 1 ≤ m) (Q : ℂ)
    (r : ℝ) (hr : 0 < r) (u : (ℂ × ℂ) × (ℂ × ℂ)) :
    0 ≤ (star u.1.1*spectralShellPlusForcing m Q r u).re+
      (star u.2.1*spectralShellMinusForcing m Q r u).re := by
  let d := ((m : ℝ)+1)*‖Q‖^(2*m)
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hD : spectralDiagonalCoefficient m Q = (d : ℂ) := spectralDiagonalCoefficient_real m Q
  have hC : ‖spectralCrossCoefficient m Q‖ ≤ d := by
    rw [spectralCrossCoefficient_norm m hm]
    dsimp only [d]
    nlinarith [pow_nonneg (norm_nonneg Q) (2*m)]
  have hp : ‖spectralCrossCoefficient m Q*(homogeneousSpectralLocalizationFactor 1 r/
      homogeneousSpectralLocalizationFactor (-1) r)‖ ≤ d := by
    rw [norm_mul,homogeneousSpectralLocalization_phase_norm 1 r hr,mul_one]
    exact hC
  have hn : ‖star (spectralCrossCoefficient m Q)*(homogeneousSpectralLocalizationFactor (-1) r/
      homogeneousSpectralLocalizationFactor 1 r)‖ ≤ d := by
    have hphase := homogeneousSpectralLocalization_phase_norm (-1) r hr
    norm_num only [neg_neg] at hphase
    rw [norm_mul,hphase,norm_star,mul_one]
    exact hC
  have h := positive_pair d _ _ u.1.1 u.2.1 hd hp hn
  simpa only [spectralShellPlusForcing,spectralShellMinusForcing,hD,
    Complex.star_def,Complex.conj_ofReal] using h

end DefocusingNLS

end OAI
