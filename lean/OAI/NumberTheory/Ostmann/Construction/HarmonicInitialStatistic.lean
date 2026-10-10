import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors
import OAI.NumberTheory.Ostmann.Construction.InitialWordLowerBound

namespace OAI

/-! # The initial statistic under the actual harmonic prime laws -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem harmonic_initial_statistic {B : Type*} [Fintype B] [Nonempty B]
    (P : Finset ℕ) {k m : ℕ} (Q : Fin k → Finset ℕ) (H : Fin m → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hH : ∀ i, H i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ p ∈ Q i, (p : ℝ)⁻¹)
    (hHmass : ∀ i, 0 < ∑ p ∈ H i, (p : ℝ)⁻¹)
    (F : ℤ → ℕ → ℂ) (hF : ∀ a p, p ∈ P → ‖F a p‖ ≤ 1)
    (E : Finset ℕ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (bin : (Fin k → P) → B) (c δ γ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hword : ∀ a ∈ E, ∀ i,
      δ * (∑ p ∈ Q i, (p : ℝ)⁻¹) ≤ ∑ p ∈ Q i, (p : ℝ)⁻¹ * (F a p).re)
    (hcells : ∀ a ∈ E, ∀ i,
      γ * (∑ p ∈ H i, (p : ℝ)⁻¹) ≤ ∑ p ∈ H i, (p : ℝ)⁻¹ * (F a p).re) :
    let μ := fun i => primeSubsetPrior P (Q i)
    let R := fun i a => ∑ p : P, (primeSubsetPrior P (H i) p : ℂ) * F a p
    ∃ b : B, (E.card : ℝ) / Fintype.card B *
        (c * (δ ^ k / Fintype.card B) ^ 2 * γ ^ (2 * m)) ≤
      ∑' a : ℤ, wordStatisticTerm ψ X
        (fun a => binnedWordAverage μ (fun _ p => F a p) bin b) R a := by
  apply initial_word_lower_bound E ψ X hX
    (fun i => primeSubsetPrior P (Q i)) (fun a _ p => F a p) bin
    (fun i a => ∑ p : P, (primeSubsetPrior P (H i) p : ℂ) * F a p)
  · exact fun i p => primeSubsetPrior_nonneg P (Q i) p
  · exact fun i => primeSubsetPrior_mass P (Q i) (hQ i) (hQmass i).ne'
  · exact fun a _ p => hF a p p.property
  · exact fun i a => primeSubsetPrior_mean_norm P (H i) (hH i) (hHmass i).ne' (F a) (hF a)
  · exact hc
  · exact hδ
  · exact hγ
  · exact hψ
  · exact hcE
  · exact fun a ha i => primeSubsetPrior_mean_positive P (Q i) (hQ i) (hQmass i) (F a) δ (hword a ha i)
  · exact fun a ha i => primeSubsetPrior_mean_positive P (H i) (hH i) (hHmass i) (F a) γ (hcells a ha i)

end Ostmann

end OAI
