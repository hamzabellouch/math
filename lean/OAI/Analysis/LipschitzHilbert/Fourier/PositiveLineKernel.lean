import OAI.Analysis.LipschitzHilbert.Estimates.LocalizedEnvelope
import OAI.Analysis.LipschitzHilbert.Estimates.EnvelopeDerivative

namespace OAI

/-! The positive horizontal convolution kernel used for the error
majorant, with its short-interval integral bound. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

def lineKernel (l x : ℝ) : ℝ := l⁻¹ * lineEnvelope 0 l 3 x

theorem lineKernel_nonneg (l x : ℝ) (hl : 0 < l) : 0 ≤ lineKernel l x :=
  mul_nonneg (inv_nonneg.mpr hl.le) (lineEnvelope_nonneg _ _ _ _)

theorem lineKernel_shift (l s x : ℝ) :
    lineKernel l (x-s) = l⁻¹ * lineEnvelope s l 3 x := by
  simp only [lineKernel, lineEnvelope, sub_zero]

theorem lineKernel_integrable (l s : ℝ) (hl : 0 < l) :
    Integrable (fun x => lineKernel l (x-s)) := by
  simp_rw [lineKernel_shift]
  exact (integrable_lineEnvelope s l hl (by decide : 1 ≤ 3)).const_mul _

theorem integral_lineKernel_le (l s : ℝ) (hl : 0 < l) :
    (∫ x, lineKernel l (x-s)) ≤ Real.pi := by
  simp_rw [lineKernel_shift]
  rw [integral_const_mul]
  calc
    _ ≤ l⁻¹ * (Real.pi*l) :=
      mul_le_mul_of_nonneg_left (integral_lineEnvelope_le s l hl (by decide : 1 ≤ 3)) (by positivity)
    _ = _ := by field_simp

theorem local_lineKernel_integral (l u r s : ℝ) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) :
    (∫ x in Icc (u-r) (u+r), lineKernel l (x-s)) ≤
      (1024 * Real.pi) * lineEnvelope u r 2 s := by
  let k := (s-u)/r
  have hs : |s-(u+r*k)| ≤ r := by
    have heq : s-(u+r*k) = 0 := by dsimp [k]; field_simp; ring
    rw [heq, abs_zero]
    exact hr.le
  have hloc := local_lineEnvelope_weighted s u l r k hl hr hlr hs
  have hw : 0 < ((1+|k|)^2/8)^2 := by positivity
  have hhor : (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
      (16 * (Real.pi*l)) * (((1+|k|)^2/8)^2)⁻¹ := by
    have h : (∫ x in Icc (u-r) (u+r), lineEnvelope s l 3 x) ≤
        (16 * (Real.pi*l)) / (((1+|k|)^2/8)^2) :=
      (le_div_iff₀ hw).mpr (by nlinarith [hloc])
    simpa only [div_eq_mul_inv] using h
  have hweight : lineEnvelope 0 1 1 k ^ 2 = lineEnvelope u r 2 s := by
    simp only [lineEnvelope, sub_zero, div_one, pow_one, ← inv_pow, k]
  simp_rw [lineKernel_shift]
  rw [integral_const_mul]
  calc
    _ ≤ l⁻¹ * ((16 * (Real.pi*l)) * (((1+|k|)^2/8)^2)⁻¹) :=
      mul_le_mul_of_nonneg_left hhor (by positivity)
    _ = (16 * Real.pi) * (((1+|k|)^2/8)^2)⁻¹ := by field_simp
    _ ≤ (16 * Real.pi) * (64 * lineEnvelope 0 1 1 k ^ 2) :=
      mul_le_mul_of_nonneg_left (box_decay_le_line_envelope k) (by positivity)
    _ = _ := by rw [hweight]; ring

end LipschitzHilbert

end

end OAI
