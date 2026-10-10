import OAI.NumberTheory.Ostmann.ZeroDensity.DensityVariableAbscissaSieve
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityGaussianSubset

namespace OAI

/-! # Variable-abscissa sieve on a concrete coefficient block -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_subset_abscissa_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T σ : ℝ, 1 ≤ T → 0 ≤ σ → σ ≤ 1 →
      ∀ U : Finset ℕ, U ⊆ Finset.Icc 1 N → ∀ a : ℕ → ℂ,
      ∀ {ι : Type} (R : Finset ι) (c : ι → PrimitiveComplexCharacter) (t β : ι → ℝ),
      (∀ i ∈ R, (c i).modulus ≤ Q) → (∀ i ∈ R, |t i| ≤ T) →
      (∀ i ∈ R, ∀ j ∈ R, c i = c j → i ≠ j → 1 ≤ |t i - t j|) →
      (∀ i ∈ R, σ ≤ β i ∧ β i ≤ 1) →
      (∑ i ∈ R, ‖densityCharacterPolynomial U
        (densityVerticalCoeff a (β i)) (c i).character (t i)‖ ^ 2) ≤
      C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + 1)) *
        (2 + 64 * (Real.log (N + 1 : ℕ)) ^ 2) * (2 + (Real.log (N + 1 : ℕ)) ^ 2) *
          ∑ n ∈ U, ‖densityVerticalCoeff a σ n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := density_variable_abscissa_sieve
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T σ hT hσ0 hσ1 U hU a ι R c t β hc ht hs hβ
  let b : ℕ → ℂ := fun n => if n ∈ U then a n else 0
  have hp (χ : PrimitiveComplexCharacter) (x u : ℝ) :
      densityCharacterPolynomial (Finset.Icc 1 N) (densityVerticalCoeff b x) χ.character u =
        densityCharacterPolynomial U (densityVerticalCoeff a x) χ.character u := by
    unfold densityCharacterPolynomial
    convert density_sum_truncate U (Finset.Icc 1 N) hU
      (fun n => densityVerticalCoeff a x n * χ.character (n : ZMod χ.modulus) *
        realAdditivePhase (-(Real.log n * u))) using 1
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ∈ U <;> simp [b, densityVerticalCoeff, hn]
  have he : (∑ n ∈ Finset.Icc 1 N, ‖densityVerticalCoeff b σ n‖ ^ 2) =
      ∑ n ∈ U, ‖densityVerticalCoeff a σ n‖ ^ 2 := by
    convert density_sum_truncate U (Finset.Icc 1 N) hU
      (fun n => ‖densityVerticalCoeff a σ n‖ ^ 2) using 1
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ∈ U <;> simp [b, densityVerticalCoeff, hn]
  simpa only [hp, he] using hb N Q hQ T σ hT hσ0 hσ1 b R c t β hc ht hs hβ

end Ostmann

end OAI
