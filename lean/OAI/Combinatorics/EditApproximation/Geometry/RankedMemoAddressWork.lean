import OAI.Combinatorics.EditApproximation.Geometry.MemoCodeWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace FiniteQuery

/-- Annotate exactly the requests made by an existing adaptive run. -/


 theorem requestWork_le {ι κ : Type*} (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (cost : ι → BinaryMemo ℚ → ℕ) (C : ℕ)
    (hcost : ∀ key memory, cost key memory ≤ C * (ask key memory).requests)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ) :
    requestWork ask cost program memory ≤ C * (run ask program memory).requests := by
  induction program generalizing memory with
  | done value => simp only [requestWork, run, Nat.mul_zero, le_refl]
  | read key next ih =>
    have hfirst := hcost key memory
    have hrest := ih (ask key memory).value (ask key memory).memory
    simp only [requestWork, run, Nat.mul_add]
    exact Nat.add_le_add hfirst hrest

end FiniteQuery

/-- Code construction is incurred for lookup and, on a miss, for insertion.
The recursive calls use the exact same returned values and cache states. -/


 theorem rankedMemoAddressWork_le {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode cost : κ → ℕ) (C : ℕ) (hcost : ∀ key, cost key ≤ C)
    (key : κ) (memory : BinaryMemo ℚ) :
    rankedMemoAddressWork rank program bits encode cost key memory ≤
      2 * C * (rankedMemoEvaluate rank program bits encode key memory).requests := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      rankedMemoAddressWork rank program bits encode cost key memory ≤
        2 * C * (rankedMemoEvaluate rank program bits encode key memory).requests := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedMemoAddressWork, rankedMemoEvaluate]
      split
      · rename_i result hfound
        simp only
        simpa only [Nat.mul_one] using (hcost key).trans (by omega : C ≤ 2 * C)
      · rename_i hfound
        simp only
        have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            rankedMemoAddressWork rank program bits encode cost child.val previous ≤
              2 * C * (rankedMemoEvaluate rank program bits encode child.val previous).requests := by
          intro child previous
          exact ih (rank child.val) (by simpa only [← hlevel] using child.property) child.val rfl previous
        have hr := FiniteQuery.requestWork_le
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          (fun child previous => rankedMemoAddressWork rank program bits encode cost child.val previous)
          (2 * C) hchildren (program key) memory
        have hk := hcost key
        rw [Nat.mul_add, Nat.mul_one]
        omega
  exact hall (rank key) key rfl memory

end EditApproximation

end OAI
