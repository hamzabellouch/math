import OAI.Analysis.LipschitzHilbert.Estimates.BoxVariationWeights

namespace OAI

/-! Local line integrals of a packet envelope, retaining both center-box
offsets. This is the positive estimate for the square-function argument. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

theorem local_lineEnvelope_weighted (s u l r k : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hlr : l ≤ r) (hs : |s - (u + r*k)| ≤ r) :
    (((1 + |k|) ^ 2 / 8) ^ 2) * (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
      16 * (Real.pi * l) := by
  have hi : IntegrableOn (lineEnvelope s l 3) (Icc (u-r) (u+r)) :=
    (integrable_lineEnvelope s l hl (by decide : 1 ≤ 3)).restrict
  have hpoint : ∀ x ∈ Icc (u-r) (u+r),
      (((1 + |k|) ^ 2 / 8) ^ 2) * lineEnvelope s l 3 x ≤ 16 * lineEnvelope s l 1 x := by
    intro x hx
    have hxu : |x-u| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hweight : (1 + |k|)^2/8 ≤ polynomialWeight (u+r*k) r 1 x := by
      simpa only [pow_one] using box_polynomial_weight u r k x 1 hr hxu
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + |k|)^2/8) hweight 2
    calc
      _ ≤ polynomialWeight (u+r*k) r 1 x ^ 2 * lineEnvelope s l 3 x :=
        mul_le_mul_of_nonneg_right hp (lineEnvelope_nonneg _ _ _ _)
      _ ≤ _ := by
        simpa only [pow_one] using polynomialWeight_sq_mul_envelope x s (u+r*k) l r 1 1 hl hr hlr hs
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ x in Icc (u-r) (u+r), 16 * lineEnvelope s l 1 x :=
      setIntegral_mono_on (hi.const_mul _) ((integrable_lineEnvelope_one s l hl).restrict.const_mul _)
        measurableSet_Icc hpoint
    _ ≤ ∫ x, 16 * lineEnvelope s l 1 x :=
      setIntegral_le_integral ((integrable_lineEnvelope_one s l hl).const_mul _)
        (Filter.Eventually.of_forall (fun _ => mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _)))
    _ = _ := by rw [integral_const_mul, integral_lineEnvelope_one s l hl]

theorem local_tileEnvelope (s z u y l r W : ℝ) (b : ℤ × ℤ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hlr : l ≤ r)
    (hs : |s - (u+r*b.1)| ≤ r) (hz : |z - (y+W*b.2)| ≤ W) :
    (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x * lineEnvelope z W 2 y) ≤
      (65536 * Real.pi) * l * boxVariationWeight b ^ 2 := by
  have hloc := local_lineEnvelope_weighted s u l r b.1 hl hr hlr hs
  have hc : 0 < ((1 + |(b.1 : ℝ)|)^2/8)^2 := by positivity
  have hhor : (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
      (16 * (Real.pi * l)) * (((1 + |(b.1 : ℝ)|)^2/8)^2)⁻¹ := by
    have h : (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
        (16 * (Real.pi * l)) / (((1 + |(b.1 : ℝ)|)^2/8)^2) :=
      (le_div_iff₀ hc).mpr (by nlinarith [hloc])
    simpa only [div_eq_mul_inv] using h
  have hver := transverse_box_envelope z y W b.2 2 hW hz
  have hprod := mul_le_mul hhor hver (lineEnvelope_nonneg _ _ _ _)
    (mul_nonneg (by positivity) (inv_nonneg.mpr hc.le))
  have hdecay := mul_le_mul (box_decay_le_line_envelope (b.1 : ℝ))
    (box_decay_le_line_envelope (b.2 : ℝ)) (by positivity) (by positivity)
  rw [integral_mul_const]
  apply hprod.trans
  have h := mul_le_mul_of_nonneg_left hdecay (by positivity : 0 ≤ 16 * (Real.pi*l))
  calc
    _ = (16 * (Real.pi*l)) *
        ((((1 + |(b.1 : ℝ)|)^2/8)^2)⁻¹ * (((1 + |(b.2 : ℝ)|)^2/8)^2)⁻¹) := by ring
    _ ≤ _ := h
    _ = _ := by unfold boxVariationWeight; ring

end LipschitzHilbert

end

end OAI
