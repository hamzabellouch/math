import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszKernel
import OAI.NumberTheory.TwoPoint.Fourier.ModFiveRectangleShift

namespace OAI

/-! Pointwise and finite-contour estimates for the quadratic Riesz kernel. -/

namespace TwoPointCorrelations

open Complex Set MeasureTheory Erdos970 intervalIntegral

lemma mrt_riesz_kernel_differentiableAt {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : s ≠ 0) (hs1 : s + 1 ≠ 0) (hs2 : s + 2 ≠ 0) :
    DifferentiableAt ℂ (mrtRieszKernel x) s := by
  unfold mrtRieszKernel
  apply DifferentiableAt.div
  · exact ((hasDerivAt_id s).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).differentiableAt.const_mul 2
  · fun_prop
  · exact mul_ne_zero (mul_ne_zero hs hs1) hs2

lemma mrt_riesz_kernel_cubic {x : ℝ} (hx : 0 < x) (σ : ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    ‖mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * x ^ σ / |t| ^ 3 := by
  have hn : |t| ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + 2‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I + 2)
  have hf : ‖(2 : ℂ) / ((σ : ℂ) + (t : ℂ) * Complex.I + 2)‖ ≤ 2 / |t| := by
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by norm_num) (abs_pos.mpr ht) hn
  rw [mrt_riesz_kernel_factor, norm_mul]
  calc
    _ ≤ (x ^ σ / t ^ 2) * (2 / |t|) :=
      mul_le_mul (modFive_perron_kernel_horizontal hx σ ht) hf (norm_nonneg _) (by positivity)
    _ = _ := by rw [← sq_abs t]; ring

lemma mrt_riesz_kernel_pole {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ‖mrtRieszKernel x (1 - (u : ℂ) * Complex.I)‖ ≤ 4 * x / (1 + u ^ 2) := by
  have he : (1 : ℂ) - (u : ℂ) * Complex.I = (1 : ℂ) + ((-u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he]
  simpa using mrt_riesz_kernel_vertical hx (by norm_num : (1 / 2 : ℝ) ≤ 1) (-u)

lemma mrt_power_integral_tail {f : ℝ → ℂ} {T D a : ℝ}
    (hT : 0 < T) (ha : 1 < a)
    (hbound : ∀ t ∈ Ioi T, ‖f t‖ ≤ D * t ^ (-a)) :
    ‖∫ t in Ioi T, f t‖ ≤ D * T ^ (1 - a) / (a - 1) := by
  have hi : IntegrableOn (fun t : ℝ => D * t ^ (-a)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -a < -1) hT).const_mul D
  have he : (∫ t in Ioi T, D * t ^ (-a)) = D * T ^ (1 - a) / (a - 1) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -a < -1) hT]
    rw [show -a + 1 = 1 - a by ring]
    rw [show 1 - a = -(a - 1) by ring]
    simp only [div_neg]
    ring
  exact (norm_integral_le_of_norm_le hi
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact hbound t ht)).trans_eq he

lemma mrt_rectangle_pole_shift_bound {f : ℂ → ℂ} {a b T B : ℝ} {A : ℂ}
    (hab : a ≤ b)
    (hres : RectangleIntegral' f ((a : ℂ) - Complex.I * (T : ℂ))
      ((b : ℂ) + Complex.I * (T : ℂ)) = A)
    (hup : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B)
    (hdown : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) * VIntegral f b (-T) T - A‖ ≤
      (‖VIntegral f a (-T) T‖ + 2 * B * (b - a)) / (2 * Real.pi) := by
  have htop : ‖HIntegral f a b T‖ ≤ B * (b - a) := by
    have hp : ∀ σ ∈ uIoc a b, ‖f ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B := by
      intro σ hσ
      exact hup σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ))
    simpa only [HIntegral, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hp
  have hbot : ‖HIntegral f a b (-T)‖ ≤ B * (b - a) := by
    have hp : ∀ σ ∈ uIoc a b, ‖f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ B := by
      intro σ hσ
      exact hdown σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ))
    simpa only [HIntegral, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hp
  have hid : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * VIntegral f b (-T) T - A =
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (VIntegral f a (-T) T + HIntegral f a b T - HIntegral f a b (-T)) := by
    rw [← hres]
    simp only [RectangleIntegral', RectangleIntegral, smul_eq_mul, Complex.sub_re,
      Complex.add_re, Complex.sub_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, one_mul, zero_sub, sub_zero, add_zero, zero_add]
    ring
  rw [hid, norm_mul]
  have hn : ‖1 / (2 * (Real.pi : ℂ) * Complex.I)‖ = 1 / (2 * Real.pi) := by
    simp [Complex.norm_real, Real.norm_eq_abs]
  rw [hn]
  have hm : ‖VIntegral f a (-T) T + HIntegral f a b T - HIntegral f a b (-T)‖ ≤
      ‖VIntegral f a (-T) T‖ + 2 * B * (b - a) := by
    exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (by linarith))
  calc
    _ ≤ (1 / (2 * Real.pi)) * (‖VIntegral f a (-T) T‖ + 2 * B * (b - a)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
