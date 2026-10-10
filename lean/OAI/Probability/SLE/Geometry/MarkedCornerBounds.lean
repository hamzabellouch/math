import OAI.Probability.SLE.Geometry.MarkedCornerChart

namespace OAI

/-! Quantitative local chart bounds for the marked corner. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

private lemma abs_max_diff_add_abs_min_diff (x y : ℝ) :
    |max x 0 - max y 0| + |min x 0 - min y 0| = |x - y| := by
  have hx := max_add_min x (0 : ℝ)
  have hy := max_add_min y (0 : ℝ)
  by_cases h : y ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr (max_le_max h le_rfl)),
      abs_of_nonneg (sub_nonneg.mpr (min_le_min h le_rfl)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    linarith
  · have h' : x ≤ y := le_of_not_ge h
    rw [abs_of_nonpos (sub_nonpos.mpr (max_le_max h' le_rfl)),
      abs_of_nonpos (sub_nonpos.mpr (min_le_min h' le_rfl)),
      abs_of_nonpos (sub_nonpos.mpr h')]
    linarith

lemma cornerMap_lipschitz : LipschitzWith 3 cornerMap := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hre : |(cornerMap z - cornerMap w).re| ≤
      |max z.re 0 - max w.re 0| + |z.im - w.im| := by
    have he : (cornerMap z - cornerMap w).re =
        -(max z.re 0 - max w.re 0) + (z.im - w.im) := by
      simp [cornerMap]
      ring
    rw [he]
    simpa only [abs_neg] using abs_add_le (-(max z.re 0 - max w.re 0)) (z.im - w.im)
  have him : |(cornerMap z - cornerMap w).im| ≤
      |min z.re 0 - min w.re 0| + |z.im - w.im| := by
    have he : (cornerMap z - cornerMap w).im =
        -(min z.re 0 - min w.re 0) - (z.im - w.im) := by
      simp [cornerMap]
      ring
    rw [he]
    simpa only [abs_neg] using abs_sub (-(min z.re 0 - min w.re 0)) (z.im - w.im)
  have hpart := abs_max_diff_add_abs_min_diff z.re w.re
  have hr := Complex.abs_re_le_norm (z - w)
  have hi := Complex.abs_im_le_norm (z - w)
  simp only [Complex.sub_re, Complex.sub_im] at hr hi
  have hb := Complex.norm_le_abs_re_add_abs_im (cornerMap z - cornerMap w)
  rw [dist_eq_norm, dist_eq_norm]
  norm_num only [NNReal.coe_ofNat]
  linarith

private lemma cornerInv_im (z : ℂ) : (cornerInv z).im = max z.re (-z.im) := by
  simp only [cornerInv, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  by_cases h : 0 ≤ -z.re - z.im
  · rw [max_eq_left h, max_eq_right (by linarith : z.re ≤ -z.im)]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith : -z.im ≤ z.re)]
    ring

lemma markedCornerChart_symm_im (w z : ℂ) :
    ((markedCornerChart w).symm z).im = max (z.re - w.re) (w.im - z.im) := by
  change (cornerInv (z - w)).im = _
  rw [cornerInv_im]
  simp only [Complex.sub_re, Complex.sub_im, neg_sub]

lemma cornerInv_lipschitz : LipschitzWith 3 cornerInv := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hr := Complex.abs_re_le_norm (z - w)
  have hi := Complex.abs_im_le_norm (z - w)
  simp only [Complex.sub_re, Complex.sub_im] at hr hi
  have hre : |(cornerInv z - cornerInv w).re| ≤ |z.re - w.re| + |z.im - w.im| := by
    have he : (cornerInv z - cornerInv w).re = -((z.re - w.re) + (z.im - w.im)) := by
      simp [cornerInv]
      ring
    rw [he, abs_neg]
    exact abs_add_le (z.re - w.re) (z.im - w.im)
  have him : |(cornerInv z - cornerInv w).im| ≤ ‖z - w‖ := by
    rw [Complex.sub_im, cornerInv_im, cornerInv_im]
    apply (abs_max_sub_max_le_max _ _ _ _).trans
    exact max_le hr (by simpa only [neg_sub_neg, abs_sub_comm] using hi)
  have hb := Complex.norm_le_abs_re_add_abs_im (cornerInv z - cornerInv w)
  rw [dist_eq_norm, dist_eq_norm]
  norm_num only [NNReal.coe_ofNat]
  linarith

lemma markedCornerChart_lipschitz (w : ℂ) : LipschitzWith 3 (markedCornerChart w) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  change dist (w + cornerMap z) (w + cornerMap z') ≤ _
  simpa only [dist_add_left] using cornerMap_lipschitz.dist_le_mul z z'

lemma markedCornerChart_inverse_lipschitz (w : ℂ) :
    LipschitzWith 3 (markedCornerChart w).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  change dist (cornerInv (z - w)) (cornerInv (z' - w)) ≤ _
  simpa only [dist_sub_right] using cornerInv_lipschitz.dist_le_mul (z - w) (z' - w)

lemma markedCornerChart_norm (w z : ℂ) : dist (markedCornerChart w z) w ≤ 3 * ‖z‖ := by
  have h := (markedCornerChart_lipschitz w).dist_le_mul z 0
  simpa only [markedCornerChart_zero, dist_zero_right, NNReal.coe_ofNat] using h

lemma markedCornerChart_norm_lower (w z : ℂ) : ‖z‖ ≤ 3 * dist (markedCornerChart w z) w := by
  have h := (markedCornerChart_inverse_lipschitz w).dist_le_mul (markedCornerChart w z) w
  have hw : (markedCornerChart w).symm w = 0 := by
    apply (markedCornerChart w).injective
    simp only [Homeomorph.apply_symm_apply, markedCornerChart_zero]
  simpa only [Homeomorph.symm_apply_apply, hw, dist_zero_right, NNReal.coe_ofNat] using h

end SLEExactGauge.Serpentine

end

end OAI
