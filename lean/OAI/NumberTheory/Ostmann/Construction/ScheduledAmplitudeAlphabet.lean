import OAI.NumberTheory.Ostmann.Construction.ScheduledAmplitude
import OAI.NumberTheory.Ostmann.Construction.InitialAmplitudeAlphabet
import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimeRanges

namespace OAI

/-! # The scheduled initial weight restricts to its actual regular-prime alphabet -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem scheduledCellAmplitude_initial_prime_alphabet {J : Type}
    (P Q : Finset ℕ) (hQP : Q ⊆ P) (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (Qμ cell : ℕ → Finset ℕ) (bulk : Finset ℕ)
    (childBound pivotBound V : ℕ → ℕ)
    (b d top : ℕ) (cs : List ℕ) (cb cd : ℝ) (sl sr : Fin d → Q) (fallback : Q)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (hμ : ∀ j, j < n → Qμ j ⊆ Q)
    (hcell : ∀ c ∈ initialSmallCellList top cs, cell c ⊆ Q) (hbulk : bulk ⊆ Q)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    scheduledCellAmplitude Subtype.val outside (fun j => primeSubsetPrior P (Qμ j))
      childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd
          (primeAlphabetEmbedding hQP ∘ sl) (primeAlphabetEmbedding hQP ∘ sr)
          (primeAlphabetEmbedding hQP fallback)) g Dq S ψ X lo hi)
      φ G Pg ρ (fun c => primeSubsetPrior P (cell c)) (primeSubsetPrior P bulk)
      top cs n (b + b) greg ggiant favorable =
    scheduledCellAmplitude Subtype.val outside (fun j => primeSubsetPrior Q (Qμ j))
      childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd
          sl sr fallback) g Dq S ψ X lo hi)
      φ G Pg ρ (fun c => primeSubsetPrior Q (cell c)) (primeSubsetPrior Q bulk)
      top cs n (b + b) greg ggiant favorable := by
  unfold scheduledCellAmplitude
  rw [scheduledRegularPrior_prime, scheduledRegularPrior_prime]
  apply movingTemplatePrimeAmplitude_initial_prime_alphabet P Q hQP q outside Qμ
    childBound pivotBound V b d (initialSmallCellList top cs).length cb cd sl sr fallback
    g Dq S ψ X lo hi φ G n (scheduledSmallLength (cs.drop n)) (b + b) Pg ρ
    (scheduledRegularPrimeSets cell bulk top (cs.drop n) n (b + b)) hμ
  intro i
  rcases i with ⟨u, j | j⟩
  · exact hcell _ (scheduledSmallCell_mem_initial top cs n j)
  · exact hbulk

end Ostmann

end OAI
