import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoKernelWork

namespace OAI

namespace EditApproximation
namespace FiniteQuery

theorem requestWork_eq_fresh_sum {ι κ : Type*}
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (cost : ι → BinaryMemo ℚ → ℕ) (weight : κ → ℕ)
    (hcost : ∀ key memory, cost key memory = ((ask key memory).freshKeys.map weight).sum)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ) :
    requestWork ask cost program memory = ((run ask program memory).freshKeys.map weight).sum := by
  induction program generalizing memory with
  | done value => rfl
  | read key next ih =>
    simp only [requestWork, run, hcost, ih, List.map_append, List.sum_append]

end FiniteQuery

/-- The local kernel annotation is exactly the sum over the freshly
evaluated keys, including the actual adaptive recursive execution. -/
theorem rankedMemoKernelWork_eq_fresh_sum {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode cost : κ → ℕ) (key : κ) (memory : BinaryMemo ℚ) :
    rankedMemoKernelWork rank program bits encode cost key memory =
      ((rankedMemoEvaluate rank program bits encode key memory).freshKeys.map cost).sum := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      rankedMemoKernelWork rank program bits encode cost key memory =
        ((rankedMemoEvaluate rank program bits encode key memory).freshKeys.map cost).sum := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedMemoKernelWork, rankedMemoEvaluate]
      split
      · rename_i result hfound
        simp only [List.map_nil, List.sum_nil]
      · rename_i hfound
        simp only [List.map_cons, List.sum_cons]
        congr 1
        apply FiniteQuery.requestWork_eq_fresh_sum
        intro child previous
        exact ih (rank child.val) (by simpa only [← hlevel] using child.property) child.val rfl previous
  exact hall (rank key) key rfl memory

end EditApproximation

end OAI
