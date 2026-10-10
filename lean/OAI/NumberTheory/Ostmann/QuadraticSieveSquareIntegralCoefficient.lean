import OAI.NumberTheory.Ostmann.QuadraticSieveSquareIntegralBase

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Complex

theorem square_gaussian_boundary_value {a t : ℝ} (ha : a≠0) (ht : 0<t) :
    ((Real.pi : ℂ)/squareGaussianParameter 0 a t)^(1/2 : ℂ) =
      (1-(Real.sign a : ℂ)*I)/(2*(Real.sqrt |a| : ℂ)*(Real.sqrt t : ℂ)) := by
  let d : ℝ := 2*Real.sqrt |a| *Real.sqrt t
  have hd : 0<d := by dsimp [d]; positivity
  have hsq : d^2=4*|a| *t := by
    dsimp [d]
    rw [mul_pow,mul_pow,Real.sq_sqrt (abs_nonneg a),Real.sq_sqrt ht.le]
    ring
  have hsign : (Real.sign a)^2=1 := by
    rcases Real.sign_apply_eq_of_ne_zero a ha with h|h <;> rw [h] <;> norm_num
  have habs : Real.sign a*|a|=a := by
    rcases ha.lt_or_gt with h|h
    · rw [Real.sign_of_neg h,abs_of_neg h]; ring
    · rw [Real.sign_of_pos h,abs_of_pos h,one_mul]
  let y : ℂ := (1-(Real.sign a : ℂ)*I)/(d : ℂ)
  have hy : 0<y.re := by
    dsimp [y]
    rw [Complex.div_ofReal_re]
    simp only [sub_re,one_re,mul_re,ofReal_re,I_re,mul_zero,ofReal_im,I_im,zero_mul,sub_self,
      sub_zero]
    exact one_div_pos.mpr hd
  have hy2 : y^2=(Real.pi : ℂ)/squareGaussianParameter 0 a t := by
    have hdne : (d : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hd.ne'
    have hane : (a : ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha
    have htne : (t : ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hpine : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hsqc : (d : ℂ)^2=4*((|a| : ℝ) : ℂ)*(t : ℂ) := by exact_mod_cast hsq
    have hsignc : (Real.sign a : ℂ)^2=1 := by exact_mod_cast hsign
    have habsc : (Real.sign a : ℂ)*((|a| : ℝ) : ℂ)=(a : ℂ) := by exact_mod_cast habs
    dsimp [y,squareGaussianParameter]
    push_cast
    rw [zero_add,div_pow,hsqc]
    have habsne : ((|a| : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (abs_pos.mpr ha).ne'
    field_simp [hane,htne,hpine,I_ne_zero,habsne]
    simp only [sub_sq,mul_pow,I_sq,hsignc]
    ring_nf
    rw [← habsc]
    ring_nf
    simp only [hsignc,I_sq]
    ring
  rw [←hy2,show (1/2 : ℂ)=(2 : ℂ)⁻¹ by norm_num,Complex.sq_cpow_two_inv hy]
  dsimp [y,d]
  push_cast
  rfl

end Ostmann.QuadraticSieve

end

end OAI
