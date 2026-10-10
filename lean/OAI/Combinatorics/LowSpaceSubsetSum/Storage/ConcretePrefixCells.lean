import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedPrefixCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedConcretePrefix

namespace OAI

/-! # The stored collector inside the bounded prefix-memory traversal -/

namespace LowSpaceSubsetSum.ConcretePrefixCells

variable {n : ℕ}

def run (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (check : Array (StoredEntry n) → ℕ → BudgetedPrefixCells.Execution Bool)
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ) :=
  BudgetedPrefixCells.run (BudgetedPrefixCells.collect D F hF B) check
    ParentLiveState.dictionary order P budget

theorem value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (check : Array (StoredEntry n) → ℕ → BudgetedPrefixCells.Execution Bool)
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ) :
    (run D F hF B check order P budget).1 =
      BudgetedConcretePrefix.run D F hF B (fun a b => (check a b).1) order P budget := by
  rw [run, BudgetedPrefixCells.value]
  simp only [BudgetedPrefixCells.collect_value, BudgetedConcretePrefix.run]

theorem dictionary_bound (I : Instance n) (C : ℕ) (hn : 10000 ≤ n)
    (d : StoredEntry.Dictionary I C) :
    ParentLiveState.dictionary d ≤ inputScale I ^ 2 * (C + 1) := by
  have hd := ParentLiveState.dictionary_scale I C d
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hc : 26 * inputScale I ≤ inputScale I ^ 2 := by nlinarith only [hu]
  have hm := Nat.mul_le_mul_right (C + 1) hc
  have hbase : inputScale I ≤ inputScale I * (C + 1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith only [hd, hu, hm, hbase]

theorem cells (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (check : Array (StoredEntry n) → ℕ → BudgetedPrefixCells.Execution Bool)
    (K : ℕ)
    (hcheck : ∀ (d : StoredEntry.Dictionary D.input D.capacity) b,
      (check d.val.records b).2 ≤ K)
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ)
    (hn : 10000 ≤ n) (hl : ∀ j, (D.pair j).left.occurrences.card ≤ D.capacity)
    (hr : ∀ j, (D.pair j).right.occurrences.card ≤ D.capacity)
    (hC : D.capacity ≤ 2 ^ n) (hB : B ≤ D.capacity) :
    (run D F hF B check order P budget).2 ≤
      BudgetedPrefixCells.frame n * (order.length + 1) +
        inputScale D.input ^ 14 * (D.capacity + 1) +
        inputScale D.input ^ 2 * (D.capacity + 1) + K :=
  BudgetedPrefixCells.cells _ _ _ _ _ _
    (fun p b => BudgetedPrefixCells.collect_cells D F hF B p b hn hl hr hC hB)
    (dictionary_bound D.input D.capacity hn) hcheck order P budget

end LowSpaceSubsetSum.ConcretePrefixCells

end OAI
