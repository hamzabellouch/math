import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Harmonic laws are independent of the containing prime alphabet -/
namespace Ostmann
open scoped Classical

def primeAlphabetEmbedding {P Q : Finset ℕ} (h : Q ⊆ P) : Q ↪ P :=
  ⟨fun q => ⟨q.val, h q.property⟩,
    fun _ _ he => Subtype.ext (congrArg (fun p : P => p.val) he)⟩

theorem primeAlphabetEmbedding_range {P Q : Finset ℕ} (h : Q ⊆ P) (p : P) :
    p ∈ Set.range (primeAlphabetEmbedding h) ↔ (p : ℕ) ∈ Q := by
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property
  · intro hp
    exact ⟨⟨p.val, hp⟩, Subtype.ext rfl⟩

theorem primeSubsetPrior_alphabet {P Q S : Finset ℕ} (h : Q ⊆ P) (q : Q) :
    primeSubsetPrior P S (primeAlphabetEmbedding h q) = primeSubsetPrior Q S q := rfl

theorem primeSubsetPrior_alphabet_support {P Q S : Finset ℕ} (h : Q ⊆ P)
    (hS : S ⊆ Q) (p : P) (hp : primeSubsetPrior P S p ≠ 0) :
    p ∈ Set.range (primeAlphabetEmbedding h) :=
  (primeAlphabetEmbedding_range h p).mpr (hS (primeSubsetPrior_support P S p hp))

end Ostmann

end OAI
