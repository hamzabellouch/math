import OAI.NumberTheory.Ostmann.HybridSieve.SamplingPolynomial
import OAI.NumberTheory.Ostmann.HybridSieve.SamplingWeights

namespace OAI

open scoped BigOperators
namespace Ostmann.HybridSieve

lemma sampling_harmonic_factor_le (Q : ℕ) :
    1 + (harmonic (Q ^ 2) : ℝ) ≤ 2 * (1 + Real.log Q) := by
  have h := harmonic_le_one_add_log (Q ^ 2)
  push_cast at h
  rw [Real.log_pow] at h
  norm_num at h
  linarith

lemma sampling_log_derivative_factor_le (N : ℕ) (hN : 0 < N) :
    2 + Real.log (2 * N : ℝ) ^ 2 ≤ 3 * (1 + Real.log (2 * N : ℝ)) ^ 2 := by
  have hnr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (2 * N : ℝ) := Real.log_nonneg (by linarith)
  nlinarith [sq_nonneg (Real.log (2 * N : ℝ))]

theorem exists_character_polynomial_sampling_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι], ∀ (N Q : ℕ) (a : ℕ → ℂ) (σ H : ℝ)
      (character : ι → PrimitiveFamily Q) (γ : ι → ℝ),
      0 < N → 0 < Q → 1 ≤ H → (∀ j, |γ j| ≤ H) →
      (∀ j k, j ≠ k → character j = character k → 1 ≤ |γ j - γ k|) →
      (∑ j, familyWeight (character j) *
        ‖Ostmann.ZeroDensity.finiteCharacterPolynomial (character j).2.val a
          (Finset.Ioc N (2 * N)) ((σ : ℂ) + (γ j : ℂ) * Complex.I)‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * H) * (1 + Real.log Q) *
          (1 + Real.log (2 * N : ℝ)) ^ 2 *
            ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  obtain ⟨C, hC, hbound⟩ := exists_character_polynomial_sampling_constant
  refine ⟨6 * C, by positivity, ?_⟩
  intro ι _ N Q a σ H character γ hN hQ hH hγ hsep
  have hQlog : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  have hH0 : 0 ≤ H := by linarith
  have hhar : 0 ≤ 1 + (harmonic (Q ^ 2) : ℝ) := by
    have h : 0 ≤ (harmonic (Q ^ 2) : ℝ) := by
      exact_mod_cast (harmonic_pos (pow_ne_zero 2 (Nat.ne_of_gt hQ))).le
    linarith
  have hE : 0 ≤ ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hfactors : (1 + (harmonic (Q ^ 2) : ℝ)) * (2 + Real.log (2 * N : ℝ) ^ 2) ≤
      (2 * (1 + Real.log Q)) * (3 * (1 + Real.log (2 * N : ℝ)) ^ 2) :=
    mul_le_mul (sampling_harmonic_factor_le Q) (sampling_log_derivative_factor_le N hN)
      (by positivity) (by positivity)
  calc
    _ ≤ C * ((N : ℝ) + (Q : ℝ) ^ 2 * H) * (1 + (harmonic (Q ^ 2) : ℝ)) *
        (2 + Real.log (2 * N : ℝ) ^ 2) *
          ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) :=
      hbound N Q a σ H character γ hN hQ hH hγ hsep
    _ ≤ C * ((N : ℝ) + (Q : ℝ) ^ 2 * H) *
        ((2 * (1 + Real.log Q)) * (3 * (1 + Real.log (2 * N : ℝ)) ^ 2)) *
          ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
      rw [mul_assoc (C * _) (1 + (harmonic (Q ^ 2) : ℝ))]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactors (by positivity)) hE
    _ = _ := by ring

theorem exists_unweighted_character_polynomial_sampling_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι], ∀ (N Q : ℕ) (a : ℕ → ℂ) (σ H : ℝ)
      (character : ι → PrimitiveFamily Q) (γ : ι → ℝ),
      0 < N → 0 < Q → 1 ≤ H → (∀ j, |γ j| ≤ H) →
      (∀ j k, j ≠ k → character j = character k → 1 ≤ |γ j - γ k|) →
      (∑ j, ‖Ostmann.ZeroDensity.finiteCharacterPolynomial (character j).2.val a
          (Finset.Ioc N (2 * N)) ((σ : ℂ) + (γ j : ℂ) * Complex.I)‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * H) * (1 + Real.log Q) *
          (1 + Real.log (2 * N : ℝ)) ^ 2 *
            ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  obtain ⟨C, hC, hbound⟩ := exists_character_polynomial_sampling_log_constant
  refine ⟨C, hC, ?_⟩
  intro ι _ N Q a σ H character γ hN hQ hH hγ hsep
  exact (unweighted_energy_le_family_weighted character _).trans
    (hbound N Q a σ H character γ hN hQ hH hγ hsep)

end Ostmann.HybridSieve

end OAI
