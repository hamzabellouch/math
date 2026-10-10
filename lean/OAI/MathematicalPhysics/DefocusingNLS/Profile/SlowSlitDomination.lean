import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowSlitKernel

namespace OAI

/-! # Uniform bounds near the nonzero imaginary spatial boundary -/

open MeasureTheory

namespace DefocusingNLS

theorem norm_cpow_le_of_norm_bounds (z r : ℂ) (b B : ℝ) (hb : 0 < b)
    (hz : b ≤ ‖z‖) (hB : ‖z‖ ≤ B) :
    ‖z ^ r‖ ≤ Real.exp (Real.pi * |r.im|) *
      b ^ (min r.re 0) * B ^ (max r.re 0) := by
  have hBpos : 0 < B := (hb.trans_le hz).trans_le hB
  have harg : -(z.arg * r.im) ≤ Real.pi * |r.im| := by
    calc
      _ ≤ |z.arg * r.im| := neg_le_abs _
      _ = |z.arg| * |r.im| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi z) (abs_nonneg _)
  have hp : ‖z‖ ^ r.re ≤ b ^ (min r.re 0) * B ^ (max r.re 0) := by
    rcases le_total 0 r.re with hr | hr
    · simp only [min_eq_right hr, max_eq_left hr, Real.rpow_zero, one_mul]
      exact Real.rpow_le_rpow (norm_nonneg _) hB hr
    · simp only [min_eq_left hr, max_eq_right hr, Real.rpow_zero, mul_one]
      exact Real.rpow_le_rpow_of_nonpos hb hz hr
  calc
    ‖z ^ r‖ ≤ ‖z‖ ^ r.re * Real.exp (-(z.arg * r.im)) := by
      simpa only [div_eq_mul_inv, ← Real.exp_neg] using Complex.norm_cpow_le z r
    _ ≤ (b ^ (min r.re 0) * B ^ (max r.re 0)) * Real.exp (Real.pi * |r.im|) :=
      mul_le_mul hp (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

theorem one_add_real_div_bounds_of_im (x : ℂ) (c M : ℝ) (hc : 0 < c)
    (hx : c ≤ |x.im|) (hM : ‖x‖ ≤ M) {u : ℝ} (hu : 0 ≤ u) :
    c / M ≤ ‖1 + (u : ℂ) / x‖ ∧ ‖1 + (u : ℂ) / x‖ ≤ 1 + u / c := by
  have hxc : c ≤ ‖x‖ := hx.trans (Complex.abs_im_le_norm x)
  have hxpos : 0 < ‖x‖ := hc.trans_le hxc
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp hxpos.ne'
  have hn : c ≤ ‖x + (u : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (x + (u : ℂ))
    simp only [Complex.add_im, Complex.ofReal_im, add_zero] at h
    exact hx.trans h
  constructor
  · have he : 1 + (u : ℂ) / x = (x + (u : ℂ)) / x := by
      field_simp
    rw [he, norm_div]
    calc
      c / M ≤ c / ‖x‖ := by gcongr
      _ ≤ ‖x + (u : ℂ)‖ / ‖x‖ := by gcongr
  · calc
      ‖1 + (u : ℂ) / x‖ ≤ 1 + u / ‖x‖ := by
        simpa only [norm_one, norm_div, Complex.norm_of_nonneg hu] using
          norm_add_le (1 : ℂ) ((u : ℂ) / x)
      _ ≤ 1 + u / c := by gcongr

theorem slowKernelSpatialDerivative_majorant_of_im (q : ℂ) (m : ℕ)
    (c M : ℝ) (hc : 0 < c) (hM : 0 < M) (x : ℂ)
    (hx : c ≤ |x.im|) (hxM : ‖x‖ ≤ M) {u : ℝ} (hu : 0 < u) :
    ‖slowKernelSpatialDerivative q m x u‖ ≤
      (‖(m : ℂ) - 1 - q‖ / c ^ 2 * Real.exp (Real.pi * |q.im|) *
        (c / M) ^ (min ((m : ℂ) - 2 - q).re 0) *
        (1 + c⁻¹) ^ (max ((m : ℂ) - 2 - q).re 0)) *
      (Real.exp (-u) * u ^ q.re +
        Real.exp (-u) * u ^ (q.re + max ((m : ℂ) - 2 - q).re 0)) := by
  let r : ℂ := (m : ℂ) - 2 - q
  let a : ℝ := max r.re 0
  have hb := one_add_real_div_bounds_of_im x c M hc hx hxM hu.le
  have hxc : c ≤ ‖x‖ := hx.trans (Complex.abs_im_le_norm x)
  have hr : Real.exp (Real.pi * |r.im|) = Real.exp (Real.pi * |q.im|) := by simp [r]
  have hp := norm_cpow_le_of_norm_bounds (1 + (u : ℂ) / x) r
    (c / M) (1 + u / c) (div_pos hc hM) hb.1 hb.2
  rw [hr] at hp
  have hpref : ‖(m : ℂ) - 1 - q‖ / ‖x‖ ^ 2 ≤ ‖(m : ℂ) - 1 - q‖ / c ^ 2 := by
    gcongr
  have hpowa : u ^ (q.re - 1) * u = u ^ q.re := by
    calc
      _ = u ^ (q.re - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = u ^ (q.re - 1 + 1) := (Real.rpow_add hu _ _).symm
      _ = _ := by congr 1; ring
  calc
    ‖slowKernelSpatialDerivative q m x u‖ =
        (‖(m : ℂ) - 1 - q‖ / ‖x‖ ^ 2) * Real.exp (-u) * u ^ q.re *
          ‖(1 + (u : ℂ) / x) ^ r‖ := by
      simp only [slowKernelSpatialDerivative, norm_mul, norm_div, norm_neg, norm_pow,
        Complex.norm_exp, Complex.neg_re, Complex.ofReal_re,
        Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re, Complex.one_re,
        Complex.norm_of_nonneg hu.le]
      rw [← hpowa]
      ring
    _ ≤ (‖(m : ℂ) - 1 - q‖ / c ^ 2) * Real.exp (-u) * u ^ q.re *
        (Real.exp (Real.pi * |q.im|) * (c / M) ^ (min r.re 0) * (1 + u / c) ^ a) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le)
          (Real.rpow_nonneg hu.le _)) hp (norm_nonneg _) (by positivity)
    _ ≤ (‖(m : ℂ) - 1 - q‖ / c ^ 2) * Real.exp (-u) * u ^ q.re *
        (Real.exp (Real.pi * |q.im|) * (c / M) ^ (min r.re 0) *
          ((1 + c⁻¹) ^ a * (1 + u ^ a))) := by
      gcongr
      exact one_add_div_rpow_le c a u hc (le_max_right _ _) hu.le
    _ = _ := by
      change _ = (‖(m : ℂ) - 1 - q‖ / c ^ 2 * Real.exp (Real.pi * |q.im|) *
        (c / M) ^ (min r.re 0) * (1 + c⁻¹) ^ a) *
        (Real.exp (-u) * u ^ q.re + Real.exp (-u) * u ^ (q.re + a))
      rw [Real.rpow_add hu]
      ring

theorem exists_slowKernelSpatialDerivative_majorant_of_im (q : ℂ) (m : ℕ)
    (hq : -1 < q.re) (c M : ℝ) (hc : 0 < c) (hM : 0 < M) :
    ∃ bound : ℝ → ℝ, IntegrableOn bound (Set.Ioi 0) ∧
      ∀ x : ℂ, c ≤ |x.im| → ‖x‖ ≤ M → ∀ u : ℝ, 0 < u →
        ‖slowKernelSpatialDerivative q m x u‖ ≤ bound u := by
  let a : ℝ := max ((m : ℂ) - 2 - q).re 0
  let C : ℝ := ‖(m : ℂ) - 1 - q‖ / c ^ 2 * Real.exp (Real.pi * |q.im|) *
    (c / M) ^ (min ((m : ℂ) - 2 - q).re 0) * (1 + c⁻¹) ^ a
  refine ⟨fun u => C * (Real.exp (-u) * u ^ q.re + Real.exp (-u) * u ^ (q.re + a)), ?_, ?_⟩
  · apply Integrable.const_mul
    exact (integrable_exp_neg_mul_rpow q.re hq).add
      (integrable_exp_neg_mul_rpow (q.re + a) (by
        have : 0 ≤ a := le_max_right _ _
        linarith))
  · intro x hx hxM u hu
    exact slowKernelSpatialDerivative_majorant_of_im q m c M hc hM x hx hxM hu

end DefocusingNLS

end OAI
