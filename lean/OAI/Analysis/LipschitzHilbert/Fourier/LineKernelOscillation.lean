import OAI.Analysis.LipschitzHilbert.Fourier.PositiveLineKernel
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! An integrable pointwise majorant for translations of a long-scale
kernel. It is used before integrating against a bounded source. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem lineEnvelope_nearby (s l x z : ℝ) (hl : 0 < l) (hz : |z-x| ≤ 2*l) :
    lineEnvelope s l 1 z ≤ 10 * lineEnvelope s l 1 x := by
  have hv : |(x-z)/l| ≤ 2 := by
    rw [abs_div, abs_of_pos hl, div_le_iff₀ hl, abs_sub_comm]
    exact hz
  have hv2 : ((x-z)/l)^2 ≤ 4 := by nlinarith [sq_abs ((x-z)/l), (abs_le.mp hv).1, (abs_le.mp hv).2]
  have heq : (x-s)/l = (z-s)/l + (x-z)/l := by ring
  have hbase : 1+((x-s)/l)^2 ≤ 10*(1+((z-s)/l)^2) := by
    rw [heq]
    nlinarith [sq_nonneg ((z-s)/l-(x-z)/l), sq_nonneg ((z-s)/l)]
  simp only [lineEnvelope, pow_one]
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < 1+((z-s)/l)^2)
    (by positivity : 0 < 1+((x-s)/l)^2)).mpr
  simpa only [one_mul] using hbase

theorem lineKernel_shift_hasDerivAt (l s x : ℝ) :
    HasDerivAt (fun z => lineKernel l (z-s))
      (l⁻¹ * deriv (lineEnvelope s l 3) x) x := by
  have h := (lineEnvelope_three_hasDerivAt s l x).differentiableAt.hasDerivAt.const_mul l⁻¹
  convert h using 1
  funext z
  exact lineKernel_shift l s z

theorem lineKernel_shift_derivative_bound (l s x z : ℝ) (hl : 0 < l)
    (hz : |z-x| ≤ 2*l) :
    ‖deriv (fun v => lineKernel l (v-s)) z‖ ≤ (60/l^2) * lineEnvelope s l 1 x := by
  rw [(lineKernel_shift_hasDerivAt l s z).deriv, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hl.le), Real.norm_eq_abs]
  calc
    _ ≤ l⁻¹ * ((6/l) * lineEnvelope s l 3 z) :=
      mul_le_mul_of_nonneg_left (lineEnvelope_three_derivative_bound s l z hl) (by positivity)
    _ ≤ l⁻¹ * ((6/l) * (10 * lineEnvelope s l 1 x)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (lineEnvelope_antitone s l z (by decide : 1 ≤ 3)).trans (lineEnvelope_nearby s l x z hl hz)
    _ = _ := by ring

theorem lineKernel_translation_bound (l s x y : ℝ) (hl : 0 < l) (hxy : |x-y| ≤ 2*l) :
    |lineKernel l (x-s) - lineKernel l (y-s)| ≤
      ((60/l^2) * |x-y|) * lineEnvelope s l 1 x := by
  have hx : x ∈ Icc (x-2*l) (x+2*l) := ⟨by linarith, by linarith⟩
  have hy : y ∈ Icc (x-2*l) (x+2*l) := by
    have h := abs_le.mp hxy
    constructor <;> linarith
  have hd (z : ℝ) (hz : z ∈ Icc (x-2*l) (x+2*l)) :
      ‖deriv (fun v => lineKernel l (v-s)) z‖ ≤ (60/l^2) * lineEnvelope s l 1 x :=
    lineKernel_shift_derivative_bound l s x z hl (abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩)
  have h := (convex_Icc (x-2*l) (x+2*l)).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (lineKernel_shift_hasDerivAt l s z).differentiableAt) hd hy hx
  simp only [Real.norm_eq_abs] at h
  exact h.trans_eq (by ring)

end LipschitzHilbert

end

end OAI
