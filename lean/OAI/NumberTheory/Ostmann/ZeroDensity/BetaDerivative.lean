import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.ZeroDensity.BetaVariation

namespace OAI

noncomputable section
open scoped BigOperators

namespace Ostmann.ZeroDensity

def finiteCharacterPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, a n * χ n * (n : ℂ) ^ (-s)

def logDerivativeCoefficients (a : ℕ → ℂ) (n : ℕ) : ℂ := -Complex.log n * a n

theorem norm_logDerivativeCoefficients_le (a : ℕ → ℂ) {n M : ℕ}
    (hn : 1 ≤ n) (hnM : n ≤ M) :
    ‖logDerivativeCoefficients a n‖ ≤ Real.log M * ‖a n‖ := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnM' : (n : ℝ) ≤ M := by exact_mod_cast hnM
  have hlog : ‖Complex.log (n : ℂ)‖ = Real.log n := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hnR)]
  rw [logDerivativeCoefficients, norm_mul, norm_neg, hlog]
  exact mul_le_mul_of_nonneg_right
    (Real.log_le_log (lt_of_lt_of_le zero_lt_one hnR) hnM') (norm_nonneg _)

def logPowerCoefficients (k : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (-Complex.log n) ^ k * a n

@[simp] theorem logPowerCoefficients_zero (a : ℕ → ℂ) :
    logPowerCoefficients 0 a = a := by
  funext n
  simp [logPowerCoefficients]

@[simp] theorem logDerivative_logPowerCoefficients (k : ℕ) (a : ℕ → ℂ) :
    logDerivativeCoefficients (logPowerCoefficients k a) =
      logPowerCoefficients (k + 1) a := by
  funext n
  simp only [logDerivativeCoefficients, logPowerCoefficients, pow_succ]
  ring

theorem norm_logPowerCoefficients_le (k : ℕ) (a : ℕ → ℂ) {n M : ℕ}
    (hn : 1 ≤ n) (hnM : n ≤ M) :
    ‖logPowerCoefficients k a n‖ ≤ (Real.log M) ^ k * ‖a n‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← logDerivative_logPowerCoefficients]
    calc
      ‖logDerivativeCoefficients (logPowerCoefficients k a) n‖ ≤
          Real.log M * ‖logPowerCoefficients k a n‖ :=
        norm_logDerivativeCoefficients_le _ hn hnM
      _ ≤ Real.log M * ((Real.log M) ^ k * ‖a n‖) :=
        mul_le_mul_of_nonneg_left ih (Real.log_nonneg (by exact_mod_cast hn.trans hnM))
      _ = _ := by rw [pow_succ]; ring

theorem finite_polynomial_beta_derivative {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (γ β : ℝ) :
    HasDerivAt
      (fun b : ℝ => finiteCharacterPolynomial χ a S ((b : ℂ) + γ * Complex.I))
      (finiteCharacterPolynomial χ (logDerivativeCoefficients a) S
        ((β : ℂ) + γ * Complex.I)) β := by
  unfold finiteCharacterPolynomial
  apply HasDerivAt.fun_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hS n hn).ne'
  have hcomplex := (((hasDerivAt_id (β : ℂ)).add_const
    ((γ : ℂ) * Complex.I)).neg).const_cpow (c := (n : ℂ)) (Or.inl hn0)
  have hreal := hcomplex.comp_ofReal
  convert hreal.const_mul (a n * χ n) using 1 <;> dsimp [logDerivativeCoefficients]
  ring

theorem finite_polynomial_beta_continuous {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (γ : ℝ) :
    Continuous (fun β : ℝ => finiteCharacterPolynomial χ a S ((β : ℂ) + γ * Complex.I)) := by
  exact continuous_iff_continuousAt.mpr fun β =>
    (finite_polynomial_beta_derivative χ a S hS γ β).continuousAt

theorem finite_polynomial_beta_variation {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (γ : ℝ)
    {σ β b : ℝ} (hσβ : σ ≤ β) (hβb : β ≤ b) :
    ‖finiteCharacterPolynomial χ a S ((β : ℂ) + γ * Complex.I)‖ ^ 2 ≤
      ‖finiteCharacterPolynomial χ a S ((σ : ℂ) + γ * Complex.I)‖ ^ 2 +
        ∫ u in σ..b,
          (‖finiteCharacterPolynomial χ a S ((u : ℂ) + γ * Complex.I)‖ ^ 2 +
           ‖finiteCharacterPolynomial χ (logDerivativeCoefficients a) S
             ((u : ℂ) + γ * Complex.I)‖ ^ 2) := by
  exact norm_sq_le_base_add_energy _ _
    (finite_polynomial_beta_continuous χ a S hS γ)
    (finite_polynomial_beta_continuous χ (logDerivativeCoefficients a) S hS γ)
    (fun β => finite_polynomial_beta_derivative χ a S hS γ β) hσβ hβb

end Ostmann.ZeroDensity

end

end OAI
