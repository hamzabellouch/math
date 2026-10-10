import OAI.NumberTheory.Ostmann.ZeroDensity.LogNormDerivative
import OAI.NumberTheory.Ostmann.ZeroDensity.SharpDigammaStrip

namespace OAI

/-! # Horizontal and vertical logarithmic derivatives of Gamma -/

namespace Ostmann

open Complex

 theorem gamma_differentiableAt_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n he
  have hr := congrArg Complex.re he
  simp only [neg_re, natCast_re] at hr
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

 theorem gamma_log_norm_horizontal (a t : ℝ) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => Real.log ‖Complex.Gamma ((x : ℂ) + t * I)‖)
      (Complex.digamma ((a : ℂ) + t * I)).re a := by
  have hz : 0 < ((a : ℂ) + t * I).re := by simpa
  have hp : HasDerivAt (fun x : ℝ => (x : ℂ) + t * I) 1 a := by
    simpa using Complex.ofRealCLM.hasDerivAt.add_const ((t : ℂ) * I)
  have hg := (gamma_differentiableAt_pos hz).hasDerivAt.scomp a hp
  have hd := hasDerivAt_log_norm hg (Complex.Gamma_ne_zero_of_re_pos hz)
  simpa only [Function.comp_apply, one_smul, digamma_def, logDeriv_apply] using hd

 theorem gamma_log_norm_vertical (a t : ℝ) (ha : 0 < a) :
    HasDerivAt (fun y : ℝ => Real.log ‖Complex.Gamma ((a : ℂ) + y * I)‖)
      (-(Complex.digamma ((a : ℂ) + t * I)).im) t := by
  have hz : 0 < ((a : ℂ) + t * I).re := by simpa
  have hp : HasDerivAt (fun y : ℝ => (a : ℂ) + y * I) I t := by
    simpa using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add (a : ℂ)
  have hg := (gamma_differentiableAt_pos hz).hasDerivAt.scomp t hp
  have hd := hasDerivAt_log_norm hg (Complex.Gamma_ne_zero_of_re_pos hz)
  simpa only [Function.comp_apply, digamma_def, logDeriv_apply, smul_eq_mul,
    mul_div_assoc, I_mul_re] using hd

end Ostmann

end OAI
