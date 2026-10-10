import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeAlphabet
import OAI.NumberTheory.Ostmann.Construction.InitialAlphabetCutoff
import OAI.NumberTheory.Ostmann.Construction.PrimeAlphabet

namespace OAI

/-! # Exact restriction of the initial two-cutoff amplitude -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplatePrimeAmplitude_initial_alphabet {A B I : Type}
    [Fintype A] [Fintype B]
    (e : B ↪ A) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (b d rinit : ℕ) (cb cd : ℝ) (sl sr : Fin d → B) (fallback : B)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → A → ℝ)
    (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e)
    (hν : ∀ i a, ν i a ≠ 0 → a ∈ Set.range e)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q
        (initialMovingDataCutoff value b d rinit cb cd (e ∘ sl) (e ∘ sr) (e fallback))
        g Dq S ψ X lo hi) φ G n r m Pg ρ ν greg ggiant favorable =
    movingTemplatePrimeAmplitude (value ∘ e) outside (fun j a => μ j (e a))
      childBound pivotBound V
      (movingOriginalLeaf (value ∘ e) q
        (initialMovingDataCutoff (value ∘ e) b d rinit cb cd sl sr fallback)
        g Dq S ψ X lo hi)
      φ G n r m Pg ρ (fun i a => ν i (e a)) greg ggiant favorable := by
  have hF : (fun {n} (T : MovingSlotData B n) s =>
      initialMovingDataCutoff value b d rinit cb cd (e ∘ sl) (e ∘ sr) (e fallback)
        (T.map e) s) =
      (fun {n} (T : MovingSlotData B n) s =>
        initialMovingDataCutoff (value ∘ e) b d rinit cb cd sl sr fallback T s) := by
    funext n T s
    exact initialMovingDataCutoff_map e value b d rinit cb cd sl sr fallback T s
  have he := movingTemplatePrimeAmplitude_original_alphabet e q value outside μ childBound pivotBound V
      (initialMovingDataCutoff value b d rinit cb cd (e ∘ sl) (e ∘ sr) (e fallback))
      g Dq S ψ X lo hi φ G n r m Pg ρ ν hμ hν greg ggiant favorable
  rw [hF] at he
  exact he

theorem movingTemplatePrimeAmplitude_initial_prime_alphabet {I : Type}
    (P Q : Finset ℕ) (hQP : Q ⊆ P) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (Qμ : ℕ → Finset ℕ) (childBound pivotBound V : ℕ → ℕ)
    (b d rinit : ℕ) (cb cd : ℝ) (sl sr : Fin d → Q) (fallback : Q)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (Qν : MovingRegularSlot n r m → Finset ℕ)
    (hμ : ∀ j, j < n → Qμ j ⊆ Q) (hν : ∀ i, Qν i ⊆ Q)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude Subtype.val outside (fun j => primeSubsetPrior P (Qμ j))
      childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d rinit cb cd
          (primeAlphabetEmbedding hQP ∘ sl) (primeAlphabetEmbedding hQP ∘ sr)
          (primeAlphabetEmbedding hQP fallback)) g Dq S ψ X lo hi)
      φ G n r m Pg ρ (fun i => primeSubsetPrior P (Qν i)) greg ggiant favorable =
    movingTemplatePrimeAmplitude Subtype.val outside (fun j => primeSubsetPrior Q (Qμ j))
      childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
        g Dq S ψ X lo hi)
      φ G n r m Pg ρ (fun i => primeSubsetPrior Q (Qν i)) greg ggiant favorable := by
  exact movingTemplatePrimeAmplitude_initial_alphabet (primeAlphabetEmbedding hQP) q
    Subtype.val outside (fun j => primeSubsetPrior P (Qμ j)) childBound pivotBound V
    b d rinit cb cd sl sr fallback g Dq S ψ X lo hi φ G n r m Pg ρ
    (fun i => primeSubsetPrior P (Qν i))
    (fun j a hj ha => primeSubsetPrior_alphabet_support hQP (hμ j hj) a ha)
    (fun i a ha => primeSubsetPrior_alphabet_support hQP (hν i) a ha)
    greg ggiant favorable

end Ostmann

end OAI
