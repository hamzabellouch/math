import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma poisson_real_mode_green {q : ℝ → ℝ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) (m a R : ℝ) :
    (∫ t in (0:ℝ)..R, (-m*a*Real.exp (-m*t))*deriv q t +
      m^2*a*Real.exp (-m*t)*q t) =
      m*a*q 0-m*a*Real.exp (-m*R)*q R := by
  have he (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-m*t))
      (Real.exp (-m*t)*(-m)) t := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul (-m)).exp
  have hder (t : ℝ) : HasDerivAt
      (fun t : ℝ => (-m*a*Real.exp (-m*t))*q t)
      ((-m*a*Real.exp (-m*t))*deriv q t +
        m^2*a*Real.exp (-m*t)*q t) t := by
    convert! ((he t).const_mul (-m*a)).mul
      ((hq.differentiable (by simp) t).hasDerivAt) using 1
    ring
  have hc : Continuous (fun t : ℝ => (-m*a*Real.exp (-m*t))*deriv q t +
      m^2*a*Real.exp (-m*t)*q t) := by
    have hd := hq.continuous_deriv (by simp)
    fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hder t) (hc.intervalIntegrable 0 R)
  convert! hh using 1
  simp only [mul_zero,Real.exp_zero,mul_one]
  ring

lemma poisson_complex_mode_green {q : ℝ → ℂ}
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) (m R : ℝ) (a : ℂ) :
    (∫ t in (0:ℝ)..R,
      (-m*Real.exp (-m*t))*(a.re*(deriv q t).re+a.im*(deriv q t).im) +
      (m^2*Real.exp (-m*t))*(a.re*(q t).re+a.im*(q t).im)) =
      m*(a.re*(q 0).re+a.im*(q 0).im) -
        m*Real.exp (-m*R)*(a.re*(q R).re+a.im*(q R).im) := by
  have hr := poisson_real_mode_green (Complex.reCLM.contDiff.comp hq) m a.re R
  have hi := poisson_real_mode_green (Complex.imCLM.contDiff.comp hq) m a.im R
  have hdr (t : ℝ) : deriv (fun x => (q x).re) t=(deriv q t).re := by
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      ((hq.differentiable (by simp) t).hasDerivAt)).deriv
  have hdi (t : ℝ) : deriv (fun x => (q x).im) t=(deriv q t).im := by
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      ((hq.differentiable (by simp) t).hasDerivAt)).deriv
  change (∫ t in (0:ℝ)..R, (-m*a.re*Real.exp (-m*t))*deriv (fun x => (q x).re) t +
      m^2*a.re*Real.exp (-m*t)*(q t).re)=_ at hr
  change (∫ t in (0:ℝ)..R, (-m*a.im*Real.exp (-m*t))*deriv (fun x => (q x).im) t +
      m^2*a.im*Real.exp (-m*t)*(q t).im)=_ at hi
  simp only [hdr] at hr
  simp only [hdi] at hi
  have hc (b : ℝ) (r : ℂ → ℝ) (h : Continuous r) :
      Continuous (fun t : ℝ => (-m*b*Real.exp (-m*t))*r (deriv q t) +
        m^2*b*Real.exp (-m*t)*r (q t)) := by
    have hd := hq.continuous_deriv (by simp)
    exact (by fun_prop)
  have hs := intervalIntegral.integral_add (μ := volume)
    ((hc a.re Complex.re Complex.continuous_re).intervalIntegrable 0 R)
    ((hc a.im Complex.im Complex.continuous_im).intervalIntegrable 0 R)
  rw [hr,hi] at hs
  convert! hs using 1
  · apply intervalIntegral.integral_congr
    intro t ht
    ring
  · simp only [Function.comp_apply,Complex.reCLM_apply,Complex.imCLM_apply]
    ring

end ScalarConductivity

end
end

end OAI
