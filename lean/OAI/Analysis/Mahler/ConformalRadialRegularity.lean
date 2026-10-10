import OAI.Analysis.Mahler.VerticalRadius

namespace OAI

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

/-- The positive-real derivative yields a strictly positive projection on
any chord of the disk. -/
theorem F_chord_re_pos {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hab : a ≠ b) : 0 < ((F b - F a) / (b-a)).re := by
  have hd : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  let g : ℝ → ℝ := fun t => (F (a+(t : ℂ)*(b-a))/(b-a)).re
  have hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt g (deriv F (a+(t : ℂ)*(b-a))).re t := by
    intro t ht
    have hf := (hasDerivAt_F_series (segment_mem_disk ha hb ht)).differentiableAt.hasDerivAt
    have hl : HasDerivAt (fun z : ℂ => a+z*(b-a)) (b-a) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (b-a)).const_add a
    have h := ((hf.comp (t : ℂ) hl).div_const (b-a)).real_of_complex
    change HasDerivAt g _ t at h
    simpa only [mul_div_cancel_right₀ _ hd] using h
  have hm : StrictMonoOn g (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hg t (interior_subset ht)).deriv]
    exact deriv_F_re_pos (segment_mem_disk ha hb (interior_subset ht))
  have h := hm (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
  dsimp [g] at h
  simp only [zero_mul, add_zero,
    one_mul, add_sub_cancel] at h
  simpa only [sub_div, Complex.sub_re, sub_pos] using h

lemma F_re_mul_re_pos {w : ℂ} (hw : ‖w‖ < 1) (hx : w.re ≠ 0) :
    0 < (F w).re * w.re := by
  have hne : -starRingEnd ℂ w ≠ w := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at this
    exact hx (by linarith)
  have h := F_chord_re_pos (a := -starRingEnd ℂ w) (by simpa using hw) hw hne
  rw [F_odd, F_conj] at h
  simp only [Complex.div_re, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply] at h
  have hd : 0 < (w.re - -w.re) * (w.re - -w.re) + (w.im - - -w.im) * (w.im - - -w.im) := by
    nlinarith [sq_pos_of_ne_zero hx]
  rw [← add_div] at h
  have hp := (div_pos_iff.mp h)
  rcases hp with hp | hp
  · nlinarith [hp.1]
  · linarith [hp.2]

lemma F_im_mul_im_pos {w : ℂ} (hw : ‖w‖ < 1) (hy : w.im ≠ 0) :
    0 < (F w).im * w.im := by
  have hne : starRingEnd ℂ w ≠ w := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    exact hy (by linarith)
  have h := F_chord_re_pos (a := starRingEnd ℂ w) (by simpa using hw) hw hne
  rw [F_conj] at h
  simp only [Complex.div_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply] at h
  have hd : 0 < (w.re-w.re)*(w.re-w.re)+(w.im- -w.im)*(w.im- -w.im) := by
    nlinarith [sq_pos_of_ne_zero hy]
  rw [← add_div] at h
  rcases div_pos_iff.mp h with hp | hp
  · nlinarith [hp.1]
  · linarith [hp.2]

lemma F_re_eq_zero_of_re_eq_zero {w : ℂ} (hx : w.re = 0) : (F w).re = 0 := by
  have he : -starRingEnd ℂ w = w := by apply Complex.ext <;> simp [hx]
  have h := congrArg Complex.re (F_odd (starRingEnd ℂ w))
  rw [he, F_conj] at h
  simp only [Complex.neg_re, Complex.conj_re] at h
  linarith

lemma F_im_eq_zero_of_im_eq_zero {w : ℂ} (hy : w.im = 0) : (F w).im = 0 := by
  have he : starRingEnd ℂ w = w := by apply Complex.ext <;> simp [hy]
  have h := congrArg Complex.im (F_conj w)
  rw [he] at h
  simp only [Complex.conj_im] at h
  linarith

lemma mul_pos_of_common_factor {a b c : ℝ} (ha : 0 < a*c) (hb : 0 < c*b) :
    0 < a*b := by
  have h := mul_pos ha hb
  have hc : 0 ≤ c*c := mul_self_nonneg c
  nlinarith [show (a*c)*(c*b) = (a*b)*(c*c) by ring]

/-- The actual F and its radial derivative have positive Euclidean pairing.
This gives radial regularity for its inverse without invoking Sard. -/
theorem F_radial_pairing_pos {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    0 < (F w).re * (w * deriv F w).re + (F w).im * (w * deriv F w).im := by
  have he : w * deriv F w = ((4/Real.pi^2 : ℝ) : ℂ) * Complex.log (cayley w) := by
    rw [(hasDerivAt_F_log hw hw0).deriv]
    dsimp [cayley]
    push_cast
    field_simp
  rw [he, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  have hx : 0 ≤ (F w).re * (Complex.log (cayley w)).re := by
    by_cases hx : w.re = 0
    · simp [F_re_eq_zero_of_re_eq_zero hx]
    · exact (mul_pos_of_common_factor (F_re_mul_re_pos hw hx) (re_mul_log_cayley_pos hw hx)).le
  have hy : 0 ≤ (F w).im * (Complex.log (cayley w)).im := by
    rw [Complex.log_im]
    by_cases hy : w.im = 0
    · simp [F_im_eq_zero_of_im_eq_zero hy]
    · exact (mul_pos_of_common_factor (F_im_mul_im_pos hw hy) (im_mul_arg_cayley_pos hw hy)).le
  have hp : 0 < (F w).re * (Complex.log (cayley w)).re +
      (F w).im * (Complex.log (cayley w)).im := by
    by_cases hx0 : w.re = 0
    · have hy0 : w.im ≠ 0 := by
        intro hy0
        exact hw0 (Complex.ext (by simpa using hx0) (by simpa using hy0))
      have := mul_pos_of_common_factor (F_im_mul_im_pos hw hy0) (im_mul_arg_cayley_pos hw hy0)
      rw [← Complex.log_im] at this
      linarith
    · have := mul_pos_of_common_factor (F_re_mul_re_pos hw hx0) (re_mul_log_cayley_pos hw hx0)
      linarith
  nlinarith [mul_pos (show 0 < 4/Real.pi^2 by positivity) hp]

end MahlerConformal

end

end OAI
