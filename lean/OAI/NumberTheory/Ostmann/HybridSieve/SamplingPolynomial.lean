import OAI.NumberTheory.Ostmann.HybridSieve.PolynomialBridge
import OAI.NumberTheory.Ostmann.HybridSieve.Sampling

namespace OAI

open scoped BigOperators
namespace Ostmann.HybridSieve

theorem exists_character_polynomial_sampling_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι], ∀ (N Q : ℕ) (a : ℕ → ℂ) (σ H : ℝ)
      (character : ι → PrimitiveFamily Q) (γ : ι → ℝ),
      0 < N → 0 < Q → 1 ≤ H → (∀ j, |γ j| ≤ H) →
      (∀ j k, j ≠ k → character j = character k → 1 ≤ |γ j - γ k|) →
      (∑ j, familyWeight (character j) *
        ‖Ostmann.ZeroDensity.finiteCharacterPolynomial (character j).2.val a
          (Finset.Ioc N (2 * N)) ((σ : ℂ) + (γ j : ℂ) * Complex.I)‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * H) * (1 + (harmonic (Q ^ 2) : ℝ)) *
          (2 + Real.log (2 * N : ℝ) ^ 2) *
            ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  obtain ⟨C, hC, hbound⟩ := exists_physical_hybrid_sampling_constant
  refine ⟨C, hC, ?_⟩
  intro ι _ N Q a σ H character γ hN hQ hH hγ hsep
  have h := hbound N Q (realPartCoefficients a σ) H character γ hN hQ hH hγ hsep
  simp_rw [physicalDyadicSum_eq_finiteCharacterPolynomial] at h
  have heq : (∑ n ∈ Finset.Ioc N (2 * N), ‖realPartCoefficients a σ n‖ ^ 2) =
      ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact norm_realPartCoefficients_sq a σ (by have := (Finset.mem_Ioc.mp hn).1; omega)
  rwa [heq] at h

end Ostmann.HybridSieve

end OAI
