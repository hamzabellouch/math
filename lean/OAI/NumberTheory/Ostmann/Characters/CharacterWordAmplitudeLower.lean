import OAI.NumberTheory.Ostmann.Characters.CharacterOriginalProductWindow
import OAI.NumberTheory.Ostmann.Construction.PrimeWordInitialAmplitude

namespace OAI

/-! # The fixed original bin gives the initial amplitude with its exact error -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem character_word_amplitude_lower (k m nc : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ)
    (hQ : ∀ i, Q i ⊆ P) (hR : ∀ i, R i ⊆ P)
    (hQmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (hRmass : ∀ i, (∑ p ∈ R i, (p : ℝ)⁻¹) ≠ 0)
    (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ)
    (hcell : ∀ i p, p ∈ R (cell i) → cellLo i ≤ p ∧ p ≤ cellHi i)
    (logX Δ τ c : ℝ) (hc : 1 ≤ c) (T : Fin k → ℝ) (a : Fin k → Bool → ℝ)
    (b : Fin (⌊4 * τ⌋₊ + 1))
    (hlo : ∀ v, Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) - c) ≤ ∏ i, cellLo ⟨v, i⟩)
    (hhi : ∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤ Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) + c))
    (hbin : ∀ y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (t : ∀ p : ℕ, ZMod p) (E : Finset ℤ) (ψ : 𝓢(ℝ, ℂ))
    (s ρ γ H : ℝ) (hs : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hH : 0 ≤ H)
    (hE : ∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp logX)).re)
    (hword : ∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - t p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b‖)
    (hmean : ∀ x ∈ E, ∀ i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (R i) p : ℂ) * χ p ((x : ZMod p) - t p)‖)
    (N : ℕ) (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p ∈ P, H * Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c) < p)
    (hN : H * Real.exp (Δ + (Fintype.card (CharacterRole k) : ℝ) * c) ≤ N) :
    let C := (Fintype.card (CharacterRole k) : ℝ) * c
    ((E.card : ℝ) * (s * ρ ^ 2 * γ ^ (2 * nc)) -
      Real.sqrt (Real.exp logX) * (‖𝓕 ψ 0‖ *
        (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) *
        ((((m + 1) + nc) + ((m + 1) + nc) : ℕ) : ℝ) ^ (((m + 1) + nc) + ((m + 1) + nc)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - (Δ - C) / 2))) / Real.sqrt (Real.exp logX) ≤
      ‖wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
        (fun i => primeSubsetPrior P (R i)) χ t ψ (Real.exp logX) N
        (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b‖ := by
  intro C
  have hwin := character_original_product_window k m nc r f cell P hP Q R cellLo cellHi
    hcell logX Δ τ c hc T a b hlo hhi hbin
  apply prime_word_fixed_bin_amplitude_norm (m + 1) nc (Nat.succ_pos _) P hP Q R hQ hR
    hQmass hRmass χ hχ t E ψ (Real.exp logX) (Real.exp_pos _)
    (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b s ρ γ hρ hγ hs hreal hE
    hword hmean H (Real.exp (Δ + C)) (Δ - C) (Real.exp_pos _) N hsupp hsmall
  · intro x hx
    have hu := (div_le_iff₀ (Real.exp_pos logX)).mp (hwin x hx).2
    simpa only [C, mul_comm] using hu
  · intro x hx
    have hl := (le_div_iff₀ (Real.exp_pos logX)).mp (hwin x hx).1
    simpa only [C, mul_comm] using hl
  · intro x hx
    have hu := (div_le_iff₀ (Real.exp_pos _)).mp (hwin x hx).2
    have hm := mul_le_mul_of_nonneg_left hu hH
    have hn := mul_le_mul_of_nonneg_right hN (Real.exp_nonneg logX)
    simpa only [Nat.cast_prod] using (show H * (∏ i, (x i : ℝ)) ≤ N * Real.exp logX by
      nlinarith only [hm, hn])

end Ostmann

end OAI
