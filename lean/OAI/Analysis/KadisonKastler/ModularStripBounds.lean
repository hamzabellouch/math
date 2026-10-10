import OAI.Analysis.KadisonKastler.ModularStripKernel

namespace OAI

/-! # Local derivative bounds in the open modular strip -/

namespace KadisonKastler

noncomputable section

theorem modularStripKernel_decay {s δ : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hy0 : δ ≤ z.im) (hy1 : z.im ≤ 1 - δ) :
    ‖modularStripKernel z s‖ ≤ Real.exp (-δ * |resolventLogFrequency s|) := by
  rw [modularStripKernel_norm hs]
  apply Real.exp_le_exp.mpr
  have ha : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1.le
  have hb : Real.log (1 - s) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  rcases le_total 0 (resolventLogFrequency s) with hlam | hlam
  · rw [abs_of_nonneg hlam]
    have hp := mul_nonneg (sub_nonneg.mpr hy1) hlam
    unfold resolventLogFrequency at *
    nlinarith
  · rw [abs_of_nonpos hlam]
    have hp := mul_nonneg (sub_nonneg.mpr hy0) (neg_nonneg.mpr hlam)
    unfold resolventLogFrequency at *
    nlinarith

theorem modularStripKernel_deriv_bound {s δ : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hδ : 0 < δ) {z : ℂ} (hy0 : δ ≤ z.im) (hy1 : z.im ≤ 1 - δ) :
    ‖(-Complex.I * (resolventLogFrequency s : ℂ)) * modularStripKernel z s‖ ≤ 1 / δ := by
  have he := modularStripKernel_decay hs hs1 hy0 hy1
  have hsmall : (δ * |resolventLogFrequency s|) *
      Real.exp (-(δ * |resolventLogFrequency s|)) ≤ 1 := by
    have ht : δ * |resolventLogFrequency s| ≤ Real.exp (δ * |resolventLogFrequency s|) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    calc
      _ ≤ Real.exp (δ * |resolventLogFrequency s|) *
          Real.exp (-(δ * |resolventLogFrequency s|)) :=
        mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  apply (le_div_iff₀ hδ).mpr
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |resolventLogFrequency s| * ‖modularStripKernel z s‖ * δ ≤
        |resolventLogFrequency s| * Real.exp (-δ * |resolventLogFrequency s|) * δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (abs_nonneg _)) hδ.le
    _ = (δ * |resolventLogFrequency s|) * Real.exp (-(δ * |resolventLogFrequency s|)) := by rw [neg_mul]; ring
    _ ≤ 1 := hsmall

end

end KadisonKastler

end OAI
