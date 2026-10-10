import OAI.NumberTheory.Ostmann.Construction.ConstructedFixedCharacterPriors
import OAI.NumberTheory.Ostmann.Characters.CharacterSelectionScales

namespace OAI

/-! # Actual endpoint tests suffice to construct the fixed character priors -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem PublishedProgressionInput.constructed_endpoint_character_priors
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : ℕ), 20000 ≤ k →
      C₀ ≤ Real.exp ((k : ℝ) / 10000) → ∀ (B z α β C : ℝ),
      0 ≤ B → 1 ≤ z → 0 < α → 0 ≤ C →
      ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤ z →
      ∀ᶠ L : ℝ in atTop, ∀ (U τ J : ℝ) (m D : ℕ),
      α * L ≤ U → U ≤ β * L → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 → 0 < τ →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m → τ / 2 ≤ J → J ≤ 4 * τ →
      (D + 1 : ℕ) ≤ Real.exp (C * L) → 5 * k ≤ D →
      ∀ (P : Finset ℕ) (G : ℕ → ℕ → ℂ) (ζ : ℂ),
      ∀ E : Finset ℕ, E.Nonempty →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, primeLogIndex p ≤ D) → ‖ζ‖ = 1 →
      (∀ x ∈ E, ∀ p ∈ P, ‖G x p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ x ∈ E, ∀ j : ℕ, j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ u : Fin k × Bool → ℝ,
      (∀ j, α * L ≤ u j ∧ u j ≤ β * L) →
      (∀ j : Fin k, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
      (∀ j, c ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
      (∀ x ∈ E, ∀ j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ X A : ℝ,
      Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∃ x₀ ∈ E,
      ∃ a : ∀ j, CharacterAnchorCell P (fun p => ζ * G x₀ p) c δ (u j),
      ∃ w : ∀ j, CharacterTargetWord P (fun p => ζ * G x₀ p) c δ U k
        (characterConstructedTargets k J (1000 * (4 : ℝ) ^ k * τ) B z m
          (fun j => (a j).index) j),
      (∀ j, 0 < (w j).indices.length) ∧
      ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 4 * C + 4) * m) ≤ S.card ∧
        let Q := characterPrimeCells w (characterAnchorCells a)
        (∀ v i, Q v i ⊆ P) ∧
        (∀ v i, (∑ p : P, primeSubsetPrior P (Q v i) p) = 1) ∧
        (∀ v i, Real.exp (-(β + 1) * L) ≤ ∑ p ∈ Q v i, (p : ℝ)⁻¹) ∧
        (∀ x ∈ S, ∀ v i, δ / 2 ≤
          ‖∑ p : P, (primeSubsetPrior P (Q v i) p : ℂ) * G x p‖) := by
  obtain ⟨C₀, hC₀, hconstruct⟩ := P0.constructed_fixed_character_priors c δ hc hδ
  refine ⟨C₀, hC₀, ?_⟩
  intro k hk hC₀k B z α β C hB hz hα hC hsize
  filter_upwards [hconstruct k hk hC₀k B z α β C hB hz hα hC hsize] with L hL
  intro U τ J m D hUL hUβ hUτ hτU hτ hm hmlo hJlo hJhi hD hkD P G ζ E hE
    hP hPD hζ hG hrich htest u hu hus hmass hmean X A hEcard
  obtain ⟨x₁, hx₁⟩ := hE
  let G' := characterEndpointExtension E x₁ G
  have hG' : ∀ x p, p ∈ P → ‖G' x p‖ ≤ 1 := by
    intro x
    exact characterEndpointExtension_property E x₁ hx₁ G
      (fun F => ∀ p ∈ P, ‖F p‖ ≤ 1) hG x
  have ht' : ∀ x j : ℕ, j ≤ 5 * k →
      c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
      (∀ p ∈ loglogShell P (U + j),
        Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
      δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (ζ * G' x p).re := by
    intro x
    exact characterEndpointExtension_property E x₁ hx₁ G
      (fun F => ∀ j : ℕ, j ≤ 5 * k →
        c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (ζ * F p).re) htest x
  have hm' : ∀ x j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
      ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * G' x p).re := by
    intro x
    exact characterEndpointExtension_property E x₁ hx₁ G
      (fun F => ∀ j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * F p).re) hmean x
  obtain ⟨a, w, hlen, x₀, hx₀, S, hSE, hS, hScard, hsub, hprob, hmass', hmeans⟩ :=
    hL U τ J m D hUL hUβ hUτ hτU hτ hm hmlo hJlo hJhi hD hkD P G' ζ
      hP hPD hζ hG' hrich ht' u hu hus hmass hm' E ⟨x₁, hx₁⟩ X A hEcard
  have hG₀ : G' x₀ = G x₀ := by
    funext p
    exact characterEndpointExtension_of_mem E x₁ G hx₀ p
  have hlocal : ∃ a₀ : ∀ j, CharacterAnchorCell P (fun p => ζ * G' x₀ p) c δ (u j),
      ∃ w₀ : ∀ j, CharacterTargetWord P (fun p => ζ * G' x₀ p) c δ U k
        (characterConstructedTargets k J (1000 * (4 : ℝ) ^ k * τ) B z m
          (fun j => (a₀ j).index) j),
      (∀ j, 0 < (w₀ j).indices.length) ∧
      ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 4 * C + 4) * m) ≤ S.card ∧
        let Q := characterPrimeCells w₀ (characterAnchorCells a₀)
        (∀ v i, Q v i ⊆ P) ∧
        (∀ v i, (∑ p : P, primeSubsetPrior P (Q v i) p) = 1) ∧
        (∀ v i, Real.exp (-(β + 1) * L) ≤ ∑ p ∈ Q v i, (p : ℝ)⁻¹) ∧
        (∀ x ∈ S, ∀ v i, δ / 2 ≤
          ‖∑ p : P, (primeSubsetPrior P (Q v i) p : ℂ) * G x p‖) := by
    refine ⟨a x₀, w x₀, hlen x₀, S, hSE, hS, hScard, hsub, hprob, hmass', ?_⟩
    intro x hx v i
    simpa only [G', characterEndpointExtension_of_mem E x₁ G (hSE hx)] using hmeans x hx v i
  have hF₀ : (fun p => ζ * G' x₀ p) = (fun p => ζ * G x₀ p) := by
    rw [hG₀]
  rw [hF₀] at hlocal
  exact ⟨x₀, hx₀, hlocal⟩

end Ostmann

end OAI
