import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularFlux
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! Differential form of the high-angular multiplier identity. -/

namespace DefocusingNLS

noncomputable def highAngularFlux (A : ℝ → ℂ) (B : ℝ → ℝ) (U : ℝ → ℂ) (t : ℝ) : ℝ :=
  (A t*star (U t)*deriv U t).re+B t*Complex.normSq (U t)

theorem hasDerivAt_complex_normSq {U : ℝ → ℂ} {U' : ℂ} {t : ℝ}
    (hU : HasDerivAt U U' t) :
    HasDerivAt (fun s => Complex.normSq (U s)) (2*(star (U t)*U').re) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hU.star.mul hU)
  convert! h using 1
  · ext s
    simp [Complex.normSq_apply,Complex.mul_re]
  · simp only [Complex.reCLM_apply,Complex.add_re,Complex.mul_re,
      Complex.star_def,Complex.conj_re,Complex.conj_im]
    ring

theorem hasDerivAt_highAngularFlux (A : ℝ → ℂ) (B : ℝ → ℝ) (U : ℝ → ℂ)
    (t : ℝ) (A' U' U'' : ℂ) (B' : ℝ)
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t)
    (hU : HasDerivAt U U' t) (hU' : HasDerivAt (deriv U) U'' t) :
    HasDerivAt (highAngularFlux A B U)
      ((A'*star (U t)*U'+A t*star U'*U'+A t*star (U t)*U'').re+
        B'*Complex.normSq (U t)+B t*(2*(star (U t)*U').re)) t := by
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    ((hA.mul hU.star).mul hU')).add (hB.mul (hasDerivAt_complex_normSq hU))
  rw [hU.deriv] at h
  convert! h using 1
  simp only [Complex.reCLM_apply,Pi.mul_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im]
  ring

/-- A local ODE yields the positive-square flux derivative with no integration
or unproved endpoint assertion. -/
theorem hasDerivAt_highAngularFlux_completed
    (A : ℝ → ℂ) (B : ℝ → ℝ) (U : ℝ → ℂ) (t : ℝ)
    (L N α αL' θ' N' h : ℝ) (A' V E U' U'' : ℂ)
    (hh : h=1 ∨ h= -1)
    (hAval : A t=(L : ℂ)+Complex.I*(h*N : ℝ))
    (hBval : B t=α*L+θ'*N/2)
    (hA : HasDerivAt A A' t)
    (hB : HasDerivAt B (αL'+θ'*N'/2) t)
    (hU : HasDerivAt U U' t) (hU' : HasDerivAt (deriv U) U'' t)
    (hODE : -A t*U''-(A'-Complex.I*(h*θ' : ℝ)*A t)*U'+V*U t=E*U t) :
    HasDerivAt (highAngularFlux A B U)
      (L*Complex.normSq (U'+((α : ℂ)-Complex.I*(h*θ'/2 : ℝ))*U t)+
        (V.re-E.re+αL'+θ'*N'/2-L*(α^2+θ'^2/4))*Complex.normSq (U t)) t := by
  have hd := hasDerivAt_highAngularFlux A B U t A' U' U'' (αL'+θ'*N'/2) hA hB hU hU'
  rw [hAval,hBval] at hd
  rw [hAval] at hODE
  rw [highAngular_corrected_flux L N α αL' θ' N' h A' V E (U t) U' U'' hh hODE] at hd
  exact hd

end DefocusingNLS

end OAI
