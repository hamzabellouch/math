import Mathlib.Algebra.BigOperators.Fin
import OAI.Analysis.Laughlin.Polynomial.LaughlinDegree

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

noncomputable def spinWeight {N Q : ℕ} (a : Configuration N Q) : ℂ :=
  ((∏ i : Fin N, Real.sqrt (Nat.choose Q (a i).val : ℝ) : ℝ) : ℂ)

noncomputable def spinPolynomial {N Q : ℕ} (ψ : State N Q) :
    MvPolynomial (SpinorVariables N) ℂ :=
  ∑ a : Configuration N Q, monomial (monomialExponent a) (spinWeight a * ψ a)

theorem monomialExponent_injective (N Q : ℕ) :
    Function.Injective (monomialExponent (N := N) (Q := Q)) := by
  intro a b hab
  funext i
  apply Fin.ext
  have h := congrArg (fun d => d (i,true)) hab
  simpa [monomialExponent] using h

theorem spinWeight_ne_zero {N Q : ℕ} (a : Configuration N Q) : spinWeight a ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Real.sqrt_ne_zero'.mpr
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a i).isLt)

theorem spinPolynomial_coeff {N Q : ℕ} (ψ : State N Q) (a : Configuration N Q) :
    (spinPolynomial ψ).coeff (monomialExponent a) = spinWeight a * ψ a := by
  classical
  simp only [spinPolynomial, coeff_sum, coeff_monomial]
  have he (b : Configuration N Q) : monomialExponent b = monomialExponent a ↔ b = a :=
    (monomialExponent_injective N Q).eq_iff
  simp_rw [he]
  simp

theorem spinPolynomial_injective (N Q : ℕ) :
    Function.Injective (spinPolynomial (N := N) (Q := Q)) := by
  intro ψ φ h
  funext a
  have hc := congrArg (fun p => p.coeff (monomialExponent a)) h
  simp only [spinPolynomial_coeff] at hc
  exact mul_left_cancel₀ (spinWeight_ne_zero a) hc

theorem state_eq_laughlin_of_polynomial {N Q : ℕ} (ψ : State N Q) (c : ℂ)
    (h : spinPolynomial ψ = C c * laughlinPolynomial N) :
    ψ = fun a => c * laughlinVector N Q a := by
  funext a
  have hc := congrArg (fun p => p.coeff (monomialExponent a)) h
  rw [spinPolynomial_coeff, coeff_C_mul] at hc
  change ψ a = c * ((laughlinPolynomial N).coeff (monomialExponent a) / spinWeight a)
  apply (mul_left_cancel₀ (spinWeight_ne_zero a))
  rw [hc]
  field_simp [spinWeight_ne_zero a]

end Laughlin

end OAI
