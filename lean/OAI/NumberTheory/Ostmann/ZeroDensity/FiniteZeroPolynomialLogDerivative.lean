import Mathlib.Analysis.Calculus.LogDeriv
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteAnalyticZeroFactors

namespace OAI

/-! # The logarithmic derivative of the actual finite zero polynomial -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem finiteZeroPolynomial_logDeriv (f : ℂ → ℂ) (S : Finset ℂ)
    (s : ℂ) (hs : s ∉ S) :
    logDeriv (finiteZeroPolynomial f S) s =
      ∑ z ∈ S, (analyticOrderNatAt f z : ℂ) / (s - z) := by
  change logDeriv (fun w => ∏ z ∈ S, (w - z) ^ analyticOrderNatAt f z) s = _
  rw [logDeriv_fun_prod]
  · apply Finset.sum_congr rfl
    intro z hz
    have hp := logDeriv_fun_pow (f := fun w : ℂ => w - z) (x := s)
      (differentiableAt_id.sub_const z) (analyticOrderNatAt f z)
    rw [hp]
    simp [logDeriv_apply, div_eq_mul_inv]
  · intro z hz
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hs (he ▸ hz)))
  · intro z _
    exact (differentiableAt_id.sub_const z).pow _

end Ostmann

end OAI
