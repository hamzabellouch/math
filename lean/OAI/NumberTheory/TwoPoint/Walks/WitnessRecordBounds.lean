import OAI.NumberTheory.TwoPoint.Bounds.ActualWitnessRecord

namespace OAI

/-! Concrete size and prime-slot bounds for an attached witness record. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mem_recordedWitnessWord {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) (t : SignedStep) :
    t ∈ recordedWitnessWord main word ↔ t ∈ main ∨ ∃ i, t ∈ word i := by
  simp [recordedWitnessWord]

lemma recordedWitnessWord_length {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) :
    (recordedWitnessWord main word).length = main.length + ∑ i, (word i).length := by
  simp [recordedWitnessWord, List.length_flatten, List.sum_ofFn]

lemma recordedWitnessWord_length_le {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) (s : ℕ) (hlen : ∀ i, (word i).length ≤ s) :
    (recordedWitnessWord main word).length ≤ main.length + n * s := by
  rw [recordedWitnessWord_length]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _i : Fin n, s := sum_le_sum (fun i _ => hlen i)
    _ = _ := by simp

theorem recordedWitnessWord_slots_le {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) (J M : ℕ)
    (hmain : ∀ t ∈ main, t.tuple.primeFactors.card ≤ J ∧ t.padding.primeFactors.card ≤ M)
    (hword : ∀ i t, t ∈ word i →
      t.tuple.primeFactors.card ≤ J ∧ t.padding.primeFactors.card ≤ M) :
    Fintype.card (ActualPrimeSlot (recordedWitnessWord main word).get) ≤
      (recordedWitnessWord main word).length * (J + M) := by
  have hvalid (t : SignedStep) (ht : t ∈ recordedWitnessWord main word) :
      t.tuple.primeFactors.card ≤ J ∧ t.padding.primeFactors.card ≤ M := by
    rcases (mem_recordedWitnessWord main word t).mp ht with ht | ⟨i, hi⟩
    · exact hmain t ht
    · exact hword i t hi
  exact actualPrimeSlot_card_le _ J M
    (fun i => (hvalid _ (List.get_mem _ i)).1)
    (fun i => (hvalid _ (List.get_mem _ i)).2)

end TwoPointCorrelations

end OAI
