import OAI.NumberTheory.Ostmann.ZeroDensity.DirichletLogDerivativeBound

namespace OAI

/-! # Uniform control of the prime-power remainder in the Euler identity -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

noncomputable def primePowerRemainder (n : ℕ) : ℂ :=
  if n.Prime then 0 else (ArithmeticFunction.vonMangoldt n : ℂ)

theorem primePowerRemainder_summable_one : LSeriesSummable primePowerRemainder (1 : ℂ) := by
  have h := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  rw [residue_one_eq_vonMangoldt] at h
  apply summable_norm_iff.mp
  convert h using 1
  funext n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [hn, ite_false, Complex.one_re, Real.rpow_one]
    by_cases hp : n.Prime
    · simp [primePowerRemainder, hp]
    · simp [primePowerRemainder, hp, Real.norm_eq_abs,
        abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]

theorem primePowerRemainder_twist_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℝ) (hs : 1 ≤ s) (n : ℕ) :
    ‖LSeries.term (fun n => χ n * primePowerRemainder n) (s : ℂ) n‖ ≤
      ‖LSeries.term primePowerRemainder (1 : ℂ) n‖ := by
  apply (LSeries.norm_term_le (s : ℂ) ?_).trans
    (LSeries.norm_term_le_of_re_le_re primePowerRemainder (by exact hs) n)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

/-- A single absolute constant bounds all higher-prime-power contributions,
uniformly in the modulus, character and real s >= 1. -/
theorem exists_primePowerRemainder_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℝ), 1 ≤ s →
      LSeriesSummable (fun n => χ n * primePowerRemainder n) (s : ℂ) ∧
        ‖LSeries (fun n => χ n * primePowerRemainder n) (s : ℂ)‖ ≤ C := by
  let C := ∑' n, ‖LSeries.term primePowerRemainder (1 : ℂ) n‖
  have hsum := primePowerRemainder_summable_one.norm
  refine ⟨C, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro q χ s hs
  have hn := primePowerRemainder_twist_norm_le χ s hs
  have hsumn : Summable (fun n => ‖LSeries.term
      (fun n => χ n * primePowerRemainder n) (s : ℂ) n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hn hsum
  have ht : LSeriesSummable (fun n => χ n * primePowerRemainder n) (s : ℂ) :=
    summable_norm_iff.mp hsumn
  refine ⟨ht, ?_⟩
  exact (norm_tsum_le_tsum_norm hsumn).trans (hsumn.tsum_le_tsum hn hsum)

end Ostmann

end OAI
