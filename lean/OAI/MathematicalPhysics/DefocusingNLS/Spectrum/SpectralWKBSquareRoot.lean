import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

namespace OAI

/-! A continuously chosen square root on the positive-real-part region,
with its derivative in the rational form needed by the WKB residual. -/

open Set
namespace DefocusingNLS

theorem spectralComplexSqrt_sq (z : ℂ) : (Complex.sqrt z)^2=z :=
  Complex.cpow_nat_inv_pow z (by decide : (2 : ℕ)≠0)

theorem spectralComplexSqrt_ne_zero (z : ℂ) (hz : z≠0) : Complex.sqrt z≠0 := by
  intro he
  have hh := spectralComplexSqrt_sq z
  rw [he,zero_pow (by decide : 2≠0)] at hh
  exact hz hh.symm

theorem spectralComplexSqrt_hasDerivAt (Z : ℝ → ℂ) (d : ℂ) (r : ℝ)
    (hZ : HasDerivAt Z d r) (hRe : 0<(Z r).re) :
    HasDerivAt (fun t => Complex.sqrt (Z t)) (d/(2*Complex.sqrt (Z r))) r := by
  have hslit : Z r ∈ Complex.slitPlane := Or.inl hRe
  have hp := ((Complex.differentiableAt_sqrt hslit).restrictScalars ℝ).comp r hZ.differentiableAt
  have hpd := hp.hasDerivAt
  have hsq := hpd.pow 2
  have heq : (fun t => (Complex.sqrt (Z t))^2)=Z := funext (fun t => spectralComplexSqrt_sq (Z t))
  change HasDerivAt (fun t => (Complex.sqrt (Z t))^2) _ r at hsq
  rw [heq] at hsq
  have he := hsq.unique hZ
  have hz : Z r≠0 := by intro hz; rw [hz] at hRe; norm_num at hRe
  have hp0 := spectralComplexSqrt_ne_zero (Z r) hz
  apply hpd.congr_deriv
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,Function.comp_apply] at he
  apply (eq_div_iff (mul_ne_zero (by norm_num) hp0)).mpr
  simpa only [mul_comm,mul_left_comm,mul_assoc] using he

theorem spectralComplexSqrt_norm_sq (z : ℂ) : ‖Complex.sqrt z‖^2=‖z‖ := by
  simpa only [norm_pow] using congrArg norm (spectralComplexSqrt_sq z)

end DefocusingNLS

end OAI
