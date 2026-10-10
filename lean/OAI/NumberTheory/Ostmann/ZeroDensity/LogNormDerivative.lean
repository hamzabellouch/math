import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-! # Real derivatives of logarithmic complex norms -/

namespace Ostmann

open Complex

 theorem hasDerivAt_log_norm {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖f t‖) (f' / f x).re x := by
  have hn : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hd := (hf.norm_sq.log (pow_ne_zero 2 hn)).div_const 2
  have he : (2 * inner ℝ (f x) f' / ‖f x‖ ^ 2) / 2 = (f' / f x).re := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply, Complex.div_re,
      ← Complex.normSq_eq_norm_sq]
    change 2 * (f' * (starRingEnd ℂ) (f x)).re / Complex.normSq (f x) / 2 = _
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [he] at hd
  convert hd using 1
  ext t
  rw [Real.log_pow]
  ring

end Ostmann

end OAI
