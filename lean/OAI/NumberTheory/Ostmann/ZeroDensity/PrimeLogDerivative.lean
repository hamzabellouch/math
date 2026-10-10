import Mathlib.Tactic.LinearCombination
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimePowerRemainder

namespace OAI

/-! # The prime logarithmic series and the actual L-function derivative -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

noncomputable def primeLogCoefficients {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n.Prime then χ n * (Real.log n : ℂ) else 0

theorem twisted_vonMangoldt_decomposition {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) =
      primeLogCoefficients χ + (fun n : ℕ => χ n * primePowerRemainder n) := by
  funext n
  by_cases hp : n.Prime
  · simp [primeLogCoefficients, primePowerRemainder, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [primeLogCoefficients, primePowerRemainder, hp]

/-- Removing prime powers from the proved Euler identity costs only an
absolute bounded error, uniformly in the character and s > 1. -/
theorem exists_primeLogDerivative_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℝ), 1 < s →
      LSeriesSummable (primeLogCoefficients χ) (s : ℂ) ∧
      ‖LSeries (primeLogCoefficients χ) (s : ℂ) +
        deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
          DirichletCharacter.LFunction χ (s : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hrem⟩ := exists_primePowerRemainder_bound
  refine ⟨C, hC, ?_⟩
  intro q hq χ s hs
  obtain ⟨hremSum, hremBound⟩ := hrem q χ s hs.le
  have ht := χ.LSeriesSummable_twist_vonMangoldt (show 1 < (s : ℂ).re from hs)
  have hdiff : (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) -
      (fun n : ℕ => χ n * primePowerRemainder n) = primeLogCoefficients χ := by
    rw [twisted_vonMangoldt_decomposition]
    exact add_sub_cancel_right _ _
  have hp : LSeriesSummable (primeLogCoefficients χ) (s : ℂ) := by
    rw [← hdiff]
    exact ht.sub hremSum
  have he := χ.LSeries_twist_vonMangoldt_eq (show 1 < (s : ℂ).re from hs)
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs] at he
  change LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) = _ at he
  rw [twisted_vonMangoldt_decomposition, LSeries_add hp hremSum] at he
  have hid : LSeries (primeLogCoefficients χ) (s : ℂ) +
      deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
        DirichletCharacter.LFunction χ (s : ℂ) =
      -LSeries (fun n : ℕ => χ n * primePowerRemainder n) (s : ℂ) := by
    linear_combination he
  refine ⟨hp, ?_⟩
  rw [hid, norm_neg]
  exact hremBound

end Ostmann

end OAI
