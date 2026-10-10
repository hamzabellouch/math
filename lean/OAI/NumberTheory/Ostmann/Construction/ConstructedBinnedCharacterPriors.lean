import OAI.NumberTheory.Ostmann.Construction.ConstructedEndpointCharacterPriors

namespace OAI

/-! # A common original word bin and all constructed cell priors -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem PublishedProgressionInput.constructed_binned_character_priors
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : ℕ), 20000 ≤ k →
      C₀ ≤ Real.exp ((k : ℝ) / 10000) → ∀ (B z α β C : ℝ),
      0 ≤ B → 1 ≤ z → 0 < α → 0 ≤ β → 0 ≤ C →
      ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤ z →
      ∀ᶠ L : ℝ in atTop, ∀ (U τ : ℝ) (m D : ℕ),
      α * L ≤ U → U ≤ β * L → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 → 0 < τ → 2 ≤ τ →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m → 1 ≤ m → L ≤ m →
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
      ∀ (bmax : ℝ) (Ubulk T₀ : Finset ℕ) (Qword : Fin (m + 1) → Finset ℕ),
      Qword 0 = T₀ → (∀ i : Fin m, Qword i.succ = Ubulk) →
      (m : ℝ) * bmax ≤ τ →
      (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
      (∀ p ∈ Ubulk, Real.log (p : ℝ) ≤ bmax) →
      (∀ x ∈ E, ∀ i, δ ≤
        ‖∑ p : P, (primeSubsetPrior P (Qword i) p : ℂ) * G x p‖) →
      ∀ u : Fin k × Bool → ℝ,
      (∀ j, α * L ≤ u j ∧ u j ≤ β * L) →
      (∀ j : Fin k, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
      (∀ j, c ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
      (∀ x ∈ E, ∀ j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ X A : ℝ, 0 < X →
      Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∃ bin : Fin (⌊4 * τ⌋₊ + 1), τ / 2 ≤ (bin.val : ℝ) ∧
      (bin.val : ℝ) ≤ 4 * τ ∧ 0 < bin.val ∧
      let J : ℝ := bin.val
      ∃ x₀ ∈ E,
      ∃ a : ∀ j, CharacterAnchorCell P (fun p => ζ * G x₀ p) c δ (u j),
      ∃ w : ∀ j, CharacterTargetWord P (fun p => ζ * G x₀ p) c δ U k
        (characterConstructedTargets k J (1000 * (4 : ℝ) ^ k * τ) B z m
          (fun j => (a j).index) j),
      (∀ j, 0 < (w j).indices.length) ∧
      ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + (β + 1) + 4 * C + 4) * m) ≤ S.card ∧
        let Q := characterPrimeCells w (characterAnchorCells a)
        (∀ v i, Q v i ⊆ P) ∧
        (∀ v i, (∑ p : P, primeSubsetPrior P (Q v i) p) = 1) ∧
        (∀ v i, Real.exp (-(β + 1) * L) ≤ ∑ p ∈ Q v i, (p : ℝ)⁻¹) ∧
        (∀ x ∈ S, ∀ v i, δ / 2 ≤
          ‖∑ p : P, (primeSubsetPrior P (Q v i) p : ℂ) * G x p‖) ∧
        (∀ x ∈ S, Real.exp (-((β + 1) - 2 * Real.log δ) * m) ≤
          ‖binnedWordAverage (fun i => primeSubsetPrior P (Qword i))
            (fun _ p => G x p)
            (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) := by
  obtain ⟨C₀, hC₀, hconstruct⟩ := P0.constructed_endpoint_character_priors c δ hc hδ
  refine ⟨C₀, hC₀, ?_⟩
  intro k hk hC₀k B z α β C hB hz hα hβ hC hsize
  filter_upwards [hconstruct k hk hC₀k B z α β C hB hz hα hC hsize,
    eventual_character_bin_count β (2 * (k : ℝ) / 10000)] with L hL hbinCount
  intro U τ m D hUL hUβ hUτ hτU hτ hτ2 hm hmlo hm1 hLm hD hkD P G ζ E hE
    hP hPD hζ hG hrich htest bmax Ubulk T₀ Qword hzero hsucc hbulksize htoplog hbulklog
    hwordMean u hu hus hmass hmean X A hX hEcard
  have hbins := hbinCount τ (by linarith only [hτ2]) (by linarith only [hUβ, hτU])
  obtain ⟨bin, hbinlo, hbinhi, hbinpos, E₁, hE₁E, hE₁, hE₁card, hword⟩ :=
    character_select_supported_bin m L X A (β + 1) δ bmax τ hm1 hLm hX
      (by linarith) hδ hδ1 hτ2 P Ubulk T₀ Qword hP hzero hsucc hbulksize htoplog hbulklog
      E hEcard (fun x _ p => G x p) hbins hwordMean
  obtain ⟨x₀, hx₀, ac, w, hlen, S, hSE₁, hS, hScard, hsub, hprob, hmass', hmeans⟩ :=
    hL U τ bin.val m D hUL hUβ hUτ hτU hτ hm hmlo hbinlo hbinhi hD hkD P G ζ E₁ hE₁
      hP hPD hζ (fun x hx => hG x (hE₁E hx)) hrich
      (fun x hx => htest x (hE₁E hx)) u hu hus hmass
      (fun x hx => hmean x (hE₁E hx)) X (A + (β + 1)) hE₁card
  refine ⟨bin, hbinlo, hbinhi, hbinpos, x₀, hE₁E hx₀, ac, w, hlen,
    S, hSE₁.trans hE₁E, hS, ?_, hsub, hprob, hmass', hmeans, ?_⟩
  · simpa only [add_assoc] using hScard
  · intro x hx
    exact hword x (hSE₁ hx)

end Ostmann

end OAI
