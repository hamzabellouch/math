import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySubsetAbscissaSieve
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDivisorBlock

namespace OAI

/-! # The variable-abscissa sieve on a divisor-bounded coefficient block -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_divisor_block_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ M N Q : ℕ, 1 ≤ M → 1 ≤ Q →
      ∀ T σ : ℝ, 1 ≤ T → 0 ≤ σ → σ ≤ 1 →
      ∀ U : Finset ℕ, U ⊆ Finset.Icc M N → ∀ a : ℕ → ℂ,
      (∀ n ∈ U, ‖a n‖ ≤ n.divisors.card) →
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∑ i ∈ R, ‖densityCharacterPolynomial U
        (densityVerticalCoeff a (β i)) (c i).character (t i)‖ ^ 2) ≤
      C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) *
        (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2) * (2 + (Real.log (N + 1 : ℕ)) ^ 2) *
          ((N : ℝ) * (1 + Real.log N) ^ 3 / (M : ℝ) ^ (2 * σ)) := by
  obtain ⟨C, hC, hb⟩ := density_subset_abscissa_sieve
  refine ⟨C, hC, ?_⟩
  intro M N Q hM hQ T σ hT hσ0 hσ1 U hU a ha ι R c t β hc ht hs hβ
  have hU1 : U ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨hMn, hnN⟩ := Finset.mem_Icc.mp (hU hn)
    exact Finset.mem_Icc.mpr ⟨hM.trans hMn, hnN⟩
  have h := hb N Q hQ T σ hT hσ0 hσ1 U hU1 a R c t β hc ht hs hβ
  exact h.trans (mul_le_mul_of_nonneg_left
    (density_divisor_block_energy U M N hM hU a ha σ hσ0) (by positivity))

end Ostmann

end OAI
