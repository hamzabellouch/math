import OAI.Probability.SLE.Geometry.MarkedAccessHook

namespace OAI

/-! An explicit plane homeomorphism takes the real axis to the two
legs of the marked access hook. It permits the same local crosscut
argument as a smooth waypoint chart without smoothing the corner. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

def cornerMap (z : ℂ) : ℂ :=
  ((-max z.re 0 + z.im : ℝ) : ℂ) + ((-min z.re 0 - z.im : ℝ) : ℂ) * Complex.I

def cornerInv (z : ℂ) : ℂ :=
  ((-z.re - z.im : ℝ) : ℂ) + ((z.re + max (-z.re - z.im) 0 : ℝ) : ℂ) * Complex.I

lemma cornerInv_cornerMap (z : ℂ) : cornerInv (cornerMap z) = z := by
  have he := max_add_min z.re (0 : ℝ)
  apply Complex.ext <;>
    simp only [cornerInv, cornerMap, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  · linarith
  · have hu : -(-max z.re 0 + z.im) - (-min z.re 0 - z.im) = z.re := by linarith
    rw [hu]
    ring

lemma cornerMap_cornerInv (z : ℂ) : cornerMap (cornerInv z) = z := by
  have he := max_add_min (-z.re - z.im) (0 : ℝ)
  apply Complex.ext <;>
    simp only [cornerInv, cornerMap, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] <;>
    linarith

def markedCornerChart (w : ℂ) : ℂ ≃ₜ ℂ where
  toFun z := w + cornerMap z
  invFun z := cornerInv (z - w)
  left_inv z := by
    change cornerInv ((w + cornerMap z) - w) = z
    rw [add_sub_cancel_left, cornerInv_cornerMap]
  right_inv z := by
    change w + cornerMap (cornerInv (z - w)) = z
    rw [cornerMap_cornerInv]
    abel
  continuous_toFun := by unfold cornerMap; fun_prop
  continuous_invFun := by unfold cornerInv; fun_prop

lemma markedCornerChart_zero (w : ℂ) : markedCornerChart w 0 = w := by
  simp [markedCornerChart, cornerMap]

lemma markedCornerChart_real_nonneg (w : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    markedCornerChart w (u : ℂ) = w - (u : ℂ) := by
  simp [markedCornerChart, cornerMap, max_eq_left hu, min_eq_right hu, sub_eq_add_neg]

lemma markedCornerChart_real_nonpos (w : ℂ) {u : ℝ} (hu : u ≤ 0) :
    markedCornerChart w (u : ℂ) = w + ((-u : ℝ) : ℂ) * Complex.I := by
  simp [markedCornerChart, cornerMap, max_eq_right hu, min_eq_left hu]

theorem markedCornerChart_real_image (w z : ℂ) :
    (∃ u : ℝ, markedCornerChart w (u : ℂ) = z) ↔
      (z.re = w.re ∧ w.im ≤ z.im) ∨ (z.im = w.im ∧ z.re ≤ w.re) := by
  constructor
  · rintro ⟨u, rfl⟩
    by_cases hu : 0 ≤ u
    · right
      rw [markedCornerChart_real_nonneg w hu]
      simp only [Complex.sub_im, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      exact ⟨trivial, by linarith⟩
    · left
      rw [markedCornerChart_real_nonpos w (le_of_not_ge hu)]
      simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero]
      exact ⟨trivial, by linarith⟩
  · rintro (⟨hre, him⟩ | ⟨him, hre⟩)
    · refine ⟨w.im - z.im, ?_⟩
      rw [markedCornerChart_real_nonpos w (by linarith)]
      apply Complex.ext <;> simp [hre]
    · refine ⟨w.re - z.re, ?_⟩
      rw [markedCornerChart_real_nonneg w (by linarith)]
      apply Complex.ext <;> simp [him]

end SLEExactGauge.Serpentine

end

end OAI
