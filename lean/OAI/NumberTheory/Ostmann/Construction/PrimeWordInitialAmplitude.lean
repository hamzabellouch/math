import OAI.NumberTheory.Ostmann.Construction.PrimeWordInitialStatistic
import OAI.NumberTheory.Ostmann.Construction.WordGraphAmplitude

namespace OAI

/-! # Repeat removal and Poisson preserve the fixed-bin initial lower bound -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem prime_word_fixed_bin_amplitude {B : Type*}
    (k nc : ℕ) (hk : 0 < k) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin k → Finset ℕ) (R : Fin nc → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ i, R i ⊆ P)
    (hQmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (hRmass : ∀ i, (∑ p ∈ R i, (p : ℝ)⁻¹) ≠ 0)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (t : ∀ p : ℕ, ZMod p) (E : Finset ℤ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (bin : (Fin k → P) → B) (b : B) (c ρ γ : ℝ)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hword : ∀ a ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((a : ZMod p) - t p)) bin b‖)
    (hcell : ∀ a ∈ E, ∀ i, γ ≤
      (∑ p : P, (primeSubsetPrior P (R i) p : ℂ) * χ p ((a : ZMod p) - t p)).re)
    (H U D : ℝ) (hU : 0 < U) (N : ℕ)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p ∈ P, H * U < p)
    (hupper : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, (∏ i, (x i : ℝ)) ≤ X * U)
    (hlower : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, X * Real.exp D ≤ ∏ i, (x i : ℝ))
    (hcut : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, H * (∏ i, (x i : ℕ)) ≤ N * X) :
    ((E.card : ℝ) * (c * ρ ^ 2 * γ ^ (2 * nc)) -
      Real.sqrt X * (‖𝓕 ψ 0‖ *
        (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) *
        (((k + nc) + (k + nc) : ℕ) : ℝ) ^ ((k + nc) + (k + nc)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2))) / Real.sqrt X ≤
      ‖wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
        (fun j => primeSubsetPrior P (R j)) χ t ψ X N bin b‖ := by
  let : Nonempty (Fin ((k + nc) + (k + nc))) := ⟨⟨0, by omega⟩⟩
  have hs := prime_word_fixed_bin_statistic k nc P Q R hQ hR hQmass hRmass χ t E ψ X hX
    bin b c ρ γ hρ hγ hψ hreal hcE hword hcell
  have hr := word_character_repeat_removal P hP Q R χ hχ t ψ X H U D hX hU hsupp hsmall
    bin b hupper hlower
  have hp := wordGraphAmplitude_eq P hP (fun i => primeSubsetPrior P (Q i))
    (fun i => primeSubsetPrior P (R i)) χ hχ t ψ X H hX N hsupp bin b hcut
  exact initial_amplitude_lower _ _ _ X _ _ hX hs hr hp

/-- The original character amplitude requires no common phase convention. -/
theorem prime_word_fixed_bin_amplitude_norm {B : Type*}
    (k nc : ℕ) (hk : 0 < k) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin k → Finset ℕ) (R : Fin nc → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ i, R i ⊆ P)
    (hQmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (hRmass : ∀ i, (∑ p ∈ R i, (p : ℝ)⁻¹) ≠ 0)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (t : ∀ p : ℕ, ZMod p) (E : Finset ℤ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (bin : (Fin k → P) → B) (b : B) (c ρ γ : ℝ)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hword : ∀ a ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((a : ZMod p) - t p)) bin b‖)
    (hcell : ∀ a ∈ E, ∀ i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R i) p : ℂ) * χ p ((a : ZMod p) - t p)‖)
    (H U D : ℝ) (hU : 0 < U) (N : ℕ)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p ∈ P, H * U < p)
    (hupper : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, (∏ i, (x i : ℝ)) ≤ X * U)
    (hlower : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, X * Real.exp D ≤ ∏ i, (x i : ℝ))
    (hcut : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, H * (∏ i, (x i : ℕ)) ≤ N * X) :
    ((E.card : ℝ) * (c * ρ ^ 2 * γ ^ (2 * nc)) -
      Real.sqrt X * (‖𝓕 ψ 0‖ *
        (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) *
        (((k + nc) + (k + nc) : ℕ) : ℝ) ^ ((k + nc) + (k + nc)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2))) / Real.sqrt X ≤
      ‖wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
        (fun j => primeSubsetPrior P (R j)) χ t ψ X N bin b‖ := by
  let : Nonempty (Fin ((k + nc) + (k + nc))) := ⟨⟨0, by omega⟩⟩
  have hs := prime_word_fixed_bin_statistic_norm k nc P Q R hQ hR hQmass hRmass χ t E ψ X hX
    bin b c ρ γ hρ hγ hψ hreal hcE hword hcell
  have hr := word_character_repeat_removal P hP Q R χ hχ t ψ X H U D hX hU hsupp hsmall
    bin b hupper hlower
  have hp := wordGraphAmplitude_eq P hP (fun i => primeSubsetPrior P (Q i))
    (fun i => primeSubsetPrior P (R i)) χ hχ t ψ X H hX N hsupp bin b hcut
  exact initial_amplitude_lower _ _ _ X _ _ hX hs hr hp

end Ostmann

end OAI
