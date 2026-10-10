import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkLogTrees

namespace OAI

/-! # Logarithmic factors indexed by the actual terminal leaves -/

namespace Ostmann
open scoped Classical BigOperators

def movingPairedLogSlots {σ : Type*} (tier : σ → ℕ) (k : ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) :
    Fin ((bulkLogLeafLists tier k (T false)).length +
      (bulkLogLeafLists tier k (T true)).length) → List σ :=
  Fin.append (fun j => (bulkLogLeafLists tier k (T false))[j])
    (fun j => (bulkLogLeafLists tier k (T true))[j])

theorem movingPairedLogSlots_count {σ : Type*} (tier : σ → ℕ) (k : ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) :
    (bulkLogLeafLists tier k (T false)).length +
      (bulkLogLeafLists tier k (T true)).length = 2 * 2 ^ n := by
  rw [bulkLogLeafLists_length, bulkLogLeafLists_length]
  omega

/-- The concrete terminal groups satisfy exactly the length hypothesis of
the weighted Page comparison. No bound on a fictitious common grouping is used. -/
theorem movingPairedLogSlots_length_le {σ : Type*} (tier : σ → ℕ) (k : ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (r : ℕ)
    (hT : ∀ b, (T b).RegularLengthLE r) :
    ∀ j, (movingPairedLogSlots tier k T j).length ≤ r := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [movingPairedLogSlots, Fin.append_left]
    exact bulkLogLeafLists_length_le tier k (T false) r (hT false) _
      (List.getElem_mem i.isLt)
  · intro i
    simp only [movingPairedLogSlots, Fin.append_right]
    exact bulkLogLeafLists_length_le tier k (T true) r (hT true) _
      (List.getElem_mem i.isLt)

end Ostmann

end OAI
