import OAI.NumberTheory.Ostmann.Construction.InitialWordLowerBound
import OAI.NumberTheory.Ostmann.Construction.WordCharacterStatistic
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # The already selected word bin gives the original positive statistic -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem prime_word_fixed_bin_statistic {B : Type*}
    (k nc : ℕ) (P : Finset ℕ) (Q : Fin k → Finset ℕ) (R : Fin nc → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ i, R i ⊆ P)
    (hQmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (hRmass : ∀ i, (∑ p ∈ R i, (p : ℝ)⁻¹) ≠ 0)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (E : Finset ℤ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (bin : (Fin k → P) → B) (b : B) (c ρ γ : ℝ)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hword : ∀ a ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((a : ZMod p) - t p)) bin b‖)
    (hcell : ∀ a ∈ E, ∀ i, γ ≤
      (∑ p : P, (primeSubsetPrior P (R i) p : ℂ) * χ p ((a : ZMod p) - t p)).re) :
    (E.card : ℝ) * (c * ρ ^ 2 * γ ^ (2 * nc)) ≤
      (wordCharacterMean Subtype.val (fun i => primeSubsetPrior P (Q i))
        (fun i => primeSubsetPrior P (R i)) χ t ψ X bin b).re := by
  let μ := fun i => primeSubsetPrior P (Q i)
  let ν := fun i => primeSubsetPrior P (R i)
  have hnorm (i : Fin nc) (a : ℤ) :
      ‖∑ p : P, (ν i p : ℂ) * χ p ((a : ZMod p) - t p)‖ ≤ 1 := by
    calc
      _ ≤ ∑ p : P, ‖(ν i p : ℂ) * χ p ((a : ZMod p) - t p)‖ := norm_sum_le _ _
      _ ≤ ∑ p : P, ν i p := by
        apply Finset.sum_le_sum
        intro p _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (primeSubsetPrior_nonneg _ _ _)]
        exact mul_le_of_le_one_right (primeSubsetPrior_nonneg _ _ _) ((χ p).norm_le_one _)
      _ = 1 := primeSubsetPrior_mass P (R i) (hR i) (hRmass i)
  have hG (a : ℤ) : ‖binnedWordAverage μ
      (fun _ p => χ p ((a : ZMod p) - t p)) bin b‖ ≤ 1 :=
    binnedWordAverage_norm_le_one μ _ bin b
      (fun i p => primeSubsetPrior_nonneg _ _ _)
      (fun i => primeSubsetPrior_mass P (Q i) (hQ i) (hQmass i))
      (fun i p => (χ p).norm_le_one _)
  have hl := wordStatistic_lower ψ X hX
    (fun a => binnedWordAverage μ (fun _ p => χ p ((a : ZMod p) - t p)) bin b)
    (fun i a => ∑ p : P, (ν i p : ℂ) * χ p ((a : ZMod p) - t p)) E
    hψ hG hnorm c ρ γ hρ hγ hcE hword
    (fun a ha i => (hcell a ha i).trans (Complex.re_le_norm _))
  rw [word_statistic_eq_character_mean Subtype.val μ ν χ t ψ X hX hreal bin b] at hl
  exact hl

/-- The statistic only uses the absolute values of the selected cell means. -/
theorem prime_word_fixed_bin_statistic_norm {B : Type*}
    (k nc : ℕ) (P : Finset ℕ) (Q : Fin k → Finset ℕ) (R : Fin nc → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ i, R i ⊆ P)
    (hQmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (hRmass : ∀ i, (∑ p ∈ R i, (p : ℝ)⁻¹) ≠ 0)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (E : Finset ℤ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (bin : (Fin k → P) → B) (b : B) (c ρ γ : ℝ)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hword : ∀ a ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((a : ZMod p) - t p)) bin b‖)
    (hcell : ∀ a ∈ E, ∀ i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R i) p : ℂ) * χ p ((a : ZMod p) - t p)‖) :
    (E.card : ℝ) * (c * ρ ^ 2 * γ ^ (2 * nc)) ≤
      (wordCharacterMean Subtype.val (fun i => primeSubsetPrior P (Q i))
        (fun i => primeSubsetPrior P (R i)) χ t ψ X bin b).re := by
  let μ := fun i => primeSubsetPrior P (Q i)
  let ν := fun i => primeSubsetPrior P (R i)
  have hnorm (i : Fin nc) (a : ℤ) :
      ‖∑ p : P, (ν i p : ℂ) * χ p ((a : ZMod p) - t p)‖ ≤ 1 := by
    calc
      _ ≤ ∑ p : P, ‖(ν i p : ℂ) * χ p ((a : ZMod p) - t p)‖ := norm_sum_le _ _
      _ ≤ ∑ p : P, ν i p := by
        apply Finset.sum_le_sum
        intro p _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (primeSubsetPrior_nonneg _ _ _)]
        exact mul_le_of_le_one_right (primeSubsetPrior_nonneg _ _ _) ((χ p).norm_le_one _)
      _ = 1 := primeSubsetPrior_mass P (R i) (hR i) (hRmass i)
  have hG (a : ℤ) : ‖binnedWordAverage μ
      (fun _ p => χ p ((a : ZMod p) - t p)) bin b‖ ≤ 1 :=
    binnedWordAverage_norm_le_one μ _ bin b
      (fun i p => primeSubsetPrior_nonneg _ _ _)
      (fun i => primeSubsetPrior_mass P (Q i) (hQ i) (hQmass i))
      (fun i p => (χ p).norm_le_one _)
  have hl := wordStatistic_lower ψ X hX
    (fun a => binnedWordAverage μ (fun _ p => χ p ((a : ZMod p) - t p)) bin b)
    (fun i a => ∑ p : P, (ν i p : ℂ) * χ p ((a : ZMod p) - t p)) E
    hψ hG hnorm c ρ γ hρ hγ hcE hword
    hcell
  rw [word_statistic_eq_character_mean Subtype.val μ ν χ t ψ X hX hreal bin b] at hl
  exact hl

end Ostmann

end OAI
