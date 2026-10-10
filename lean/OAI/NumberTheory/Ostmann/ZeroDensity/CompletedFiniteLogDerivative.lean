import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedDiskZeros
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteZeroPolynomialLogDerivative

namespace OAI

/-! # Logarithmic derivatives with precisely the disk zeros removed -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def completedZeroPartialFraction (χ : PrimitiveComplexCharacter) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ z ∈ completedDiskZeros χ R, (analyticOrderNatAt χ.completed z : ℂ) / (s - z)

theorem completed_logDeriv_remove_finite (χ : PrimitiveComplexCharacter) (R : ℝ)
    (g : ℂ → ℂ) (hg : ∀ z, AnalyticAt ℂ g z)
    (he : ∀ z, χ.completed z = finiteZeroPolynomial χ.completed (completedDiskZeros χ R) z * g z)
    (s : ℂ) (hs : χ.completed s ≠ 0) :
    logDeriv χ.completed s - completedZeroPartialFraction χ R s = logDeriv g s := by
  have hsS : s ∉ completedDiskZeros χ R := fun h => hs ((mem_completedDiskZeros χ R s).mp h).2
  have hgn : g s ≠ 0 := by
    intro h
    exact hs (by rw [he, h, mul_zero])
  have hfun : χ.completed = fun z => finiteZeroPolynomial χ.completed (completedDiskZeros χ R) z * g z := funext he
  have hsplit : logDeriv χ.completed s =
      logDeriv (finiteZeroPolynomial χ.completed (completedDiskZeros χ R)) s + logDeriv g s := by
    conv_lhs => rw [hfun]
    exact logDeriv_fun_mul s (finiteZeroPolynomial_ne_zero _ _ s hsS) hgn
      (finiteZeroPolynomial_analytic _ _ s).differentiableAt (hg s).differentiableAt
  rw [hsplit, finiteZeroPolynomial_logDeriv _ _ s hsS]
  simp [completedZeroPartialFraction]

end Ostmann

end OAI
