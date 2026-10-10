import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionInvolutive
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

namespace OAI

/-! The literal hyperbolic three-space action used in DR v3, Section 5.1.
The determinant calculation is kept explicit, before using the action
to transport the cubic theta series. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaMobiusDenominator (g : SL(2,ℂ)) (p : ℂ × ℝ) : ℝ :=
  Complex.normSq (g 1 0*p.1+g 1 1)+Complex.normSq (g 1 0)*p.2^2

def cubicThetaMobiusNumerator (g : SL(2,ℂ)) (p : ℂ × ℝ) : ℂ :=
  (g 0 0*p.1+g 0 1)*star (g 1 0*p.1+g 1 1)+g 0 0*star (g 1 0)*(p.2^2:ℝ)

def cubicThetaMobius (g : SL(2,ℂ)) (p : ℂ × ℝ) : ℂ × ℝ :=
  (cubicThetaMobiusNumerator g p/(cubicThetaMobiusDenominator g p:ℂ),
    p.2/cubicThetaMobiusDenominator g p)

lemma cubicThetaMobius_det (g : SL(2,ℂ)) :
    g 0 0*g 1 1-g 0 1*g 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using g.property

lemma cubicThetaMobius_denominator_pos (g : SL(2,ℂ)) {p : ℂ × ℝ}
    (hp : 0 < p.2) : 0 < cubicThetaMobiusDenominator g p := by
  by_cases hc : g 1 0 = 0
  · have hd : g 1 1 ≠ 0 := by
      intro hd
      have h := cubicThetaMobius_det g
      rw [hc,hd,mul_zero,mul_zero,sub_zero] at h
      exact zero_ne_one h
    simpa only [cubicThetaMobiusDenominator,hc,zero_mul,zero_add,
      Complex.normSq_zero,mul_zero,add_zero] using Complex.normSq_pos.mpr hd
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (mul_pos (Complex.normSq_pos.mpr hc) (sq_pos_of_pos hp))

lemma cubicThetaMobius_height_pos (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    0 < (cubicThetaMobius g p).2 :=
  div_pos hp (cubicThetaMobius_denominator_pos g hp)

private lemma normSq_lagrange (A B a b : ℂ) (t : ℝ) :
    (Complex.normSq A+Complex.normSq a*t)*(Complex.normSq B+Complex.normSq b*t)-
      Complex.normSq (A*star B+a*star b*(t:ℂ)) =
        Complex.normSq (A*b-a*B)*t := by
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

lemma cubicThetaMobius_radius (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaRadius (cubicThetaMobius g p) =
      (Complex.normSq (g 0 0*p.1+g 0 1)+Complex.normSq (g 0 0)*p.2^2)/
        cubicThetaMobiusDenominator g p := by
  have hD := ne_of_gt (cubicThetaMobius_denominator_pos g hp)
  have h := normSq_lagrange (g 0 0*p.1+g 0 1) (g 1 0*p.1+g 1 1)
    (g 0 0) (g 1 0) (p.2^2)
  have he : (g 0 0*p.1+g 0 1)*g 1 0-g 0 0*(g 1 0*p.1+g 1 1) = -1 := by
    linear_combination -cubicThetaMobius_det g
  rw [he,Complex.normSq_neg,Complex.normSq_one,one_mul] at h
  change cubicThetaRadius (cubicThetaMobius g p) = _
  unfold cubicThetaRadius cubicThetaMobius
  simp only [Complex.normSq_div,Complex.normSq_ofReal,div_pow]
  rw [← pow_two (cubicThetaMobiusDenominator g p)]
  change (Complex.normSq (g 0 0*p.1+g 0 1)+Complex.normSq (g 0 0)*p.2^2)*
    cubicThetaMobiusDenominator g p-Complex.normSq (cubicThetaMobiusNumerator g p) = p.2^2 at h
  field_simp
  linear_combination -h

end CubicFirstMoment

end

end OAI
