import OAI.NumberTheory.TwoPoint.Halasz.HalaszCircleWindow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! A uniform logarithmic Taylor remainder for the short multiplicative
shifts in the double mean-value method. -/
namespace TwoPointCorrelations

open Finset Complex

noncomputable def halaszLogTaylor (k : ℕ) (z h : ℝ) : ℝ :=
  ∑ i∈range k,(-1:ℝ)^i*(h/z)^(i+1)/(i+1)

lemma halasz_log_taylor_remainder (k : ℕ) {z h : ℝ}
    (hz : 0<z) (hh : 0≤h) (hhz : h≤z/2) :
    |Real.log (z+h)-Real.log z-halaszLogTaylor k z h|≤2*(h/z)^(k+1) := by
  have hu : 0≤h/z := div_nonneg hh hz.le
  have hu2 : h/z≤1/2 := (div_le_iff₀ hz).mpr (by linarith)
  have hu1 : |-(h/z)|<1 := by rw [abs_neg,abs_of_nonneg hu]; linarith
  have hl := Real.abs_log_sub_add_sum_range_le hu1 k
  have he : (∑ i∈range k, (-(h/z))^(i+1)/((i+1:ℕ):ℝ)) =
      -halaszLogTaylor k z h := by
    rw [halaszLogTaylor,← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    rw [neg_eq_neg_one_mul,mul_pow,pow_succ (-1:ℝ)]
    push_cast
    ring
  simp only [Nat.cast_add,Nat.cast_one] at he
  rw [he,sub_neg_eq_add,abs_neg,abs_of_nonneg hu] at hl
  have hlog : Real.log (z+h)=Real.log z+Real.log (1+h/z) := by
    rw [← Real.log_mul hz.ne' (by linarith : 1+h/z≠0)]
    congr 1
    field_simp
  rw [hlog]
  have hden : (h/z)^(k+1)/(1-h/z)≤2*(h/z)^(k+1) := by
    apply (div_le_iff₀ (by linarith : 0<1-h/z)).mpr
    nlinarith [pow_nonneg hu (k+1)]
  convert hl.trans hden using 1
  congr 1
  ring

lemma halasz_exp_phase_lipschitz (x y : ℝ) :
    ‖Complex.exp (Complex.I*(x:ℂ))-Complex.exp (Complex.I*(y:ℂ))‖≤|x-y| := by
  have he : Complex.exp (Complex.I*(x:ℂ))-Complex.exp (Complex.I*(y:ℂ))=
      Complex.exp (Complex.I*(y:ℂ))*
        (Complex.exp (Complex.I*((x-y:ℝ):ℂ))-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_exp_I_mul_ofReal,one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y))

lemma halasz_log_taylor_phase (k : ℕ) {z h : ℝ} (t : ℝ)
    (hz : 0<z) (hh : 0≤h) (hhz : h≤z/2) :
    ‖Complex.exp (Complex.I*((t*Real.log (z+h):ℝ):ℂ))-
      Complex.exp (Complex.I*((t*(Real.log z+halaszLogTaylor k z h):ℝ):ℂ))‖≤
      2*|t| *(h/z)^(k+1) := by
  have hp := halasz_exp_phase_lipschitz (t*Real.log (z+h))
    (t*(Real.log z+halaszLogTaylor k z h))
  have he : t*Real.log (z+h)-t*(Real.log z+halaszLogTaylor k z h)=
      t*(Real.log (z+h)-Real.log z-halaszLogTaylor k z h) := by ring
  rw [he,abs_mul] at hp
  exact hp.trans (by
    have hh := mul_le_mul_of_nonneg_left (halasz_log_taylor_remainder k hz hh hhz)
      (abs_nonneg t)
    nlinarith)

end TwoPointCorrelations

end OAI
