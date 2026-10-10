import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoWork

namespace OAI

/-! A fixed-width binary memo has bounded height on every execution,
including failed approximation events and repeated lookups. This bound
uses the actual returned tree and does not count a complete table allocation. -/

namespace EditApproximation

namespace BinaryMemo

def height {α : Type*} : BinaryMemo α → ℕ
  | .empty => 0
  | .node _ left right => max left.height right.height + 1

theorem child_height {α : Type*} (tree : BinaryMemo α) :
    tree.left.height ≤ tree.height ∧ tree.right.height ≤ tree.height := by
  cases tree with
  | empty => exact ⟨le_rfl, le_rfl⟩
  | node value left right =>
    exact ⟨(le_max_left _ _).trans (Nat.le_succ _),
      (le_max_right _ _).trans (Nat.le_succ _)⟩

theorem insert_height {α : Type*} (tree : BinaryMemo α) (key : List Bool) (value : α) :
    (tree.insert key value).height ≤ max tree.height (key.length + 1) := by
  induction key generalizing tree with
  | nil =>
    cases tree <;> simp only [insert, left, right, height, List.length_nil] <;> omega
  | cons bit key ih =>
    cases tree with
    | empty =>
      have h := ih (.empty : BinaryMemo α)
      cases bit <;> simp only [insert, left, right, height, List.length_cons] at * <;> omega
    | node old left right =>
      have hl := ih left
      have hr := ih right
      cases bit <;> simp only [insert, BinaryMemo.left, BinaryMemo.right, height, List.length_cons] at * <;> omega

theorem nodes_le_height {α : Type*} (tree : BinaryMemo α) :
    tree.nodes + 1 ≤ 2 ^ tree.height := by
  induction tree with
  | empty => rfl
  | node value left right hl hr =>
    have hleft := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (le_max_left left.height right.height)
    have hright := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (le_max_right left.height right.height)
    simp only [nodes, height, pow_succ]
    omega

end BinaryMemo

namespace FiniteQuery

theorem run_height_bound {ι κ : Type*}
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ) (bound : ℕ)
    (hask : ∀ key memory, (ask key memory).memory.height ≤ max memory.height bound)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ) :
    (run ask program memory).memory.height ≤ max memory.height bound := by
  induction program generalizing memory with
  | done result => exact le_max_left _ _
  | read key next ih =>
    have hf := hask key memory
    have hr := ih (ask key memory).value (ask key memory).memory
    change (run ask (next (ask key memory).value) (ask key memory).memory).memory.height ≤ _
    exact hr.trans (max_le (hf.trans (le_refl _)) (le_max_right _ _))

end FiniteQuery

theorem rankedMemoEvaluate_height_bound {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (key : κ) (memory : BinaryMemo ℚ) :
    (rankedMemoEvaluate rank program bits encode key memory).memory.height ≤
      max memory.height (bits + 1) := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      (rankedMemoEvaluate rank program bits encode key memory).memory.height ≤
        max memory.height (bits + 1) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · exact le_max_left _ _
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            (rankedMemoEvaluate rank program bits encode child.val previous).memory.height ≤
              max previous.height (bits + 1) := by
          intro child previous
          exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous
        have hr := FiniteQuery.run_height_bound _ (bits + 1) hchildren (program key) memory
        simp only [BinaryMemo.insertCosted_spec]
        exact (BinaryMemo.insert_height _ _ _).trans
          (max_le hr (by simp only [binaryMemoKey_length]; exact le_max_right _ _))
  exact hall (rank key) key rfl memory

theorem rankedMemoEvaluate_nodes_bound {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (key : κ) :
    (rankedMemoEvaluate rank program bits encode key .empty).memory.nodes + 1 ≤ 2 ^ (bits + 1) := by
  have h := rankedMemoEvaluate_height_bound rank program bits encode key .empty
  simp only [BinaryMemo.height, max_eq_right (Nat.zero_le _)] at h
  exact (BinaryMemo.nodes_le_height _).trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h)

end EditApproximation

end OAI
