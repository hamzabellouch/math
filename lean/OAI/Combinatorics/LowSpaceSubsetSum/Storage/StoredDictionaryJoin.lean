import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredEntry
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.JoinUserMap
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedStreamJoin

namespace OAI

/-! # Executed bounded-list dictionary joins and semantic erasure

The callback carries the dictionary invariant on every reachable state.
Erasure preserves the original trie, record order, join counters and halt flag.
Reader and record semantics are specialized separately.
-/

namespace LowSpaceSubsetSum.StoredDictionaryJoin

universe u v s t
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {n : ℕ}

def erase (I : Instance n) (C : ℕ) (r : StoredEntry.Dictionary I C) :=
  StoredEntry.mapDictionary r.val

@[simp] theorem erase_empty (I : Instance n) (C : ℕ) :
    erase I C (StoredEntry.empty I C) = RecordedDictionary.empty := by
  simp [erase, StoredEntry.empty, CountedDictionaryCallback.empty,
    StoredEntry.mapDictionary, RecordedDictionary.empty]

def run (I : Instance n) (C : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ)
    (emit : α → β → Option (StoredEntry n) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (B fuel₁ fuel₂ control : ℕ) (s₁ : σ₁) (s₂ : σ₂) :=
  CountedStreamJoin.runAcc read₁ key₁ read₂ key₂ cells (StoredEntry.report I C emit) clone
    B fuel₁ fuel₂ control (StreamJoin.start s₁ s₂ (StoredEntry.empty I C))

theorem run_value (I : Instance n) (C : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (cells : β → ℕ)
    (emit : α → β → Option (StoredEntry n) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (hclone : ∀ s, (clone s).1 = s)
    (B fuel₁ fuel₂ control : ℕ) (s₁ : σ₁) (s₂ : σ₂) :
    StreamJoin.mapStopped (erase I C)
      (run I C read₁ key₁ read₂ key₂ cells emit clone B fuel₁ fuel₂ control s₁ s₂).1 =
      StreamJoin.stopped (fun s => (read₁ s).1) (fun x => (key₁ x).1)
        (fun s => (read₂ s).1) (fun y => (key₂ y).1)
        (RecordedDictionary.callback C (WeightEncoding.entryKey I)
          (fun x y => (emit x y).1.map StoredEntry.semantic))
        B fuel₁ fuel₂ control s₁ s₂ RecordedDictionary.empty := by
  let report := fun x y r => (StoredEntry.report I C emit x y r).1
  let report' := RecordedDictionary.callback C (WeightEncoding.entryKey I)
    (fun x y => (emit x y).1.map StoredEntry.semantic)
  have hf : ∀ x y r, report' x y (erase I C r) =
      (erase I C (report x y r).1, (report x y r).2) := by
    intro x y r
    exact (StoredEntry.report_value I C emit x y r).symm
  rw [run, CountedStreamJoin.runAcc_value read₁ key₁ read₂ key₂ cells
    (StoredEntry.report I C emit) clone hclone]
  change StreamJoin.mapStopped (erase I C)
      (StreamJoin.stoppedAcc _ _ _ _ report B fuel₁ fuel₂ control _) = _
  rw [StreamJoin.stoppedAcc_mapUser _ _ _ _ report report' (erase I C) hf]
  change StreamJoin.stoppedAcc _ _ _ _ report' B fuel₁ fuel₂ control
    (StreamJoin.start s₁ s₂ (erase I C (StoredEntry.empty I C))) = _
  rw [erase_empty]
  rfl

end LowSpaceSubsetSum.StoredDictionaryJoin

end OAI
