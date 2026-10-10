import OAI.Probability.SLE.Geometry.RoundedConnector

namespace OAI

/-! Embedded normal bands over the quarter-circles of the connector. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

def quarterNormal (r t a : ℝ) : ℂ :=
  quarterBend r t + (a : ℂ) * Complex.I * quarterTangent r t

def upperQuarterNormal (r t a : ℝ) : ℂ :=
  upperQuarter r t + (a : ℂ) * Complex.I * upperQuarterTangent r t

lemma quarterNormal_eq (r t a : ℝ) :
    quarterNormal r t a = ((r - (r + a) * Real.cos (t / r) : ℝ) : ℂ) +
      (((r + a) * Real.sin (t / r) : ℝ) : ℂ) * Complex.I := by
  rw [quarterNormal, quarterBend_eq, quarterTangent_eq]
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

lemma quarter_angle_bound {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) (quarterLength r)) :
    t / r ∈ Icc (0 : ℝ) (Real.pi / 2) := by
  constructor
  · exact div_nonneg ht.1 hr.le
  · apply (div_le_iff₀ hr).mpr
    dsimp only [quarterLength] at ht
    linarith [ht.2]

lemma quarterNormal_bounds {r t a : ℝ} (hr : 1 < r)
    (ht : t ∈ Icc (0 : ℝ) (quarterLength r)) (ha : |a| ≤ 1) :
    -1 ≤ (quarterNormal r t a).re ∧ (quarterNormal r t a).re ≤ r ∧
    0 ≤ (quarterNormal r t a).im ∧ (quarterNormal r t a).im ≤ r + 1 := by
  have hr0 : 0 < r := by linarith
  have hθ := quarter_angle_bound hr0 ht
  have hsin : 0 ≤ Real.sin (t / r) := Real.sin_nonneg_of_mem_Icc
    ⟨hθ.1, hθ.2.trans (by linarith [Real.pi_pos])⟩
  have hcos : 0 ≤ Real.cos (t / r) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have ha' := abs_le.mp ha
  have hR : 0 < r + a := by linarith
  simp only [quarterNormal_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, mul_one, zero_add]
  have hc0 := mul_nonneg hR.le hcos
  have hc1 := mul_le_mul_of_nonneg_left (Real.cos_le_one (t / r)) hR.le
  have hs0 := mul_nonneg hR.le hsin
  have hs1 := mul_le_mul_of_nonneg_left (Real.sin_le_one (t / r)) hR.le
  exact ⟨by linarith, by linarith, hs0, by linarith⟩

lemma upperQuarterNormal_reverse (r t a : ℝ) :
    upperQuarterNormal r t a = ((r : ℂ) + (r : ℂ) * Complex.I) -
      quarterNormal r (quarterLength r - t) (-a) := by
  simp only [upperQuarterNormal, upperQuarter, upperQuarterTangent, quarterNormal,
    Complex.ofReal_neg]
  ring

lemma upperQuarterNormal_bounds {r t a : ℝ} (hr : 1 < r)
    (ht : t ∈ Icc (0 : ℝ) (quarterLength r)) (ha : |a| ≤ 1) :
    0 ≤ (upperQuarterNormal r t a).re ∧ (upperQuarterNormal r t a).re ≤ r + 1 ∧
    -1 ≤ (upperQuarterNormal r t a).im ∧ (upperQuarterNormal r t a).im ≤ r := by
  have ht' : quarterLength r - t ∈ Icc (0 : ℝ) (quarterLength r) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have ha' : |-a| ≤ 1 := by simpa only [abs_neg] using ha
  obtain ⟨hre0, hre1, him0, him1⟩ := quarterNormal_bounds hr ht' ha'
  simp only [upperQuarterNormal_reverse, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end SLEExactGauge.Serpentine

end

end OAI
