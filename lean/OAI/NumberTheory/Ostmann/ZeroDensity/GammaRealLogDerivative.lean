import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import OAI.NumberTheory.Ostmann.ZeroDensity.GammaContourBounds

namespace OAI

/-! # Logarithmic derivatives of the archimedean Gamma factor -/

namespace Ostmann

open Complex

theorem gammaReal_logDeriv (s : ℂ) (hs : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    logDeriv Complex.Gammaℝ s = (Complex.digamma (s / 2) - Complex.log (Real.pi : ℂ)) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  let p : ℂ → ℂ := fun u => (Real.pi : ℂ) ^ (-u / 2)
  have hpne : p s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hpi)
  have hp := (((hasDerivAt_id s).neg).div_const 2).const_cpow (.inl hpi)
  have hplog : logDeriv p s = -(Complex.log (Real.pi : ℂ)) / 2 := by
    rw [logDeriv_apply, show deriv p s = p s * Complex.log (Real.pi : ℂ) * (-1 / 2) from hp.deriv]
    field_simp [hpne]
  have hgamma := ((hasDerivAt_id s).div_const 2).logDeriv_Gamma hs
  simp only [id_eq] at hgamma
  have hgd : DifferentiableAt ℂ (fun u : ℂ => Complex.Gamma (u / 2)) s :=
    (Complex.differentiableAt_Gamma _ hs).comp s (differentiableAt_id.div_const 2)
  have he : Complex.Gammaℝ = fun u => p u * Complex.Gamma (u / 2) := rfl
  rw [he, logDeriv_fun_mul (f := p) (g := fun u => Complex.Gamma (u / 2)) s hpne
    (Complex.Gamma_ne_zero hs) hp.differentiableAt hgd, hplog, hgamma]
  ring

end Ostmann

end OAI
