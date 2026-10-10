import OAI.NumberTheory.Ostmann.Arithmetic.MovingIndexedProbability
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLineIntegration

namespace OAI

/-! # Actual prime samples in the fixed line-probability coordinates -/

namespace Ostmann
open scoped Classical

noncomputable def movingSampledInternalProbability {A : Type*} {N n : ℕ}
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (T : Bool → MovingSlotData (Fin N) n) (x : Fin N → A) (rep : Fin N) : ℝ :=
  letI : Fact (prime (x rep)).Prime := ⟨hprime (x rep)⟩
  internalLineProbability true
    (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
      (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).a)
    (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
      (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).b)

theorem movingSampledIndexedProbability {A : Type*} {N n : ℕ}
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime) (x : Fin N → A)
    (T : Bool → MovingSlotData (Fin N) n) (tier : Fin N → ℕ)
    (hdisjoint : ∀ i j, tier i ≠ tier j → prime (x i) ≠ prime (x j))
    (hlevels : ∀ side, (T side).Levels tier)
    (rep : Fin N) (base : MovingPairRepresentativeOccurrences T rep)
    (hunique : ∀ i, prime (x i) = prime (x rep) → i = rep)
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod (prime (x rep))) ≠ 0)) :
    letI : Fact (prime (x rep)).Prime := ⟨hprime (x rep)⟩
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
        (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).a)
      (fun j => MovingSlotReversal.naturalReduction (prime (x rep)) (fun i => prime (x i))
        (movingPrimeOccurrenceLine (fun i => prime (x i)) T (prime (x rep)) j).b) =
      movingSlotLineProbability (fun a => (prime a : ℤ)) prime hprime
        (fun o => (movingIndexedOccurrence T rep base o).path)
        (fun o => (movingIndexedOccurrence T rep base o).current) true x (x rep) := by
  let : Fact (prime (x rep)).Prime := ⟨hprime (x rep)⟩
  have h := movingInternalBaseProbability_indexed_normalized T tier (fun i => prime (x i))
    (fun i => hprime (x i)) hdisjoint hlevels rep base hunique hf
  simpa only [movingSlotLineProbability, integerLineReduction,
    MovingSlotReversal.naturalReduction, Int.cast_natCast, movingIndexedLine] using h

end Ostmann

end OAI
