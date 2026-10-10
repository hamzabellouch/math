import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BudgetedNodeCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PreparedCheckerCells

namespace OAI

/-! # The concrete stored-mask filter realizes the traversal cell bound -/

namespace LowSpaceSubsetSum.StoredNodeCells

open StoredSeparatorCheck

variable {n g : ℕ}

def prepare (b : Block n g) (lo hi : ℕ) (xs ys : List (StoredEntry n)) :=
  BudgetedNodeCells.prepare
    (fun x l h => StoredQueryCells.query b.row x b.leftStore b.leftSize b.steps l h)
    (fun y l h => StoredQueryCells.query b.row y b.rightStore b.rightSize b.steps l h)
    lo hi xs ys

theorem prepare_value (b : Block n g) (lo hi : ℕ) (xs ys : List (StoredEntry n)) :
    (prepare b lo hi xs ys).1 = BudgetedSeparatorNode.prepare b.leftQuery b.rightQuery lo hi xs ys := by
  have hl : (fun x l h =>
      (StoredQueryCells.query b.row x b.leftStore b.leftSize b.steps l h).1) = b.leftQuery := by
    funext x l h
    exact PreparedCheckerCells.query_left_value b x l h
  have hr : (fun x l h =>
      (StoredQueryCells.query b.row x b.rightStore b.rightSize b.steps l h).1) = b.rightQuery := by
    funext x l h
    exact PreparedCheckerCells.query_right_value b x l h
  unfold prepare
  rw [BudgetedNodeCells.prepare_value, hl, hr]

theorem prepare_cells (b : Block n g) (lo hi : ℕ) (xs ys : List (StoredEntry n)) :
    (prepare b lo hi xs ys).2 ≤
      8 * (xs.length + ys.length + 1) + PreparedCheckerCells.scratch n g :=
  BudgetedNodeCells.prepare_cells _ _ _
    (fun x l h => PreparedCheckerCells.query_left_cells b x l h)
    (fun y l h => PreparedCheckerCells.query_right_cells b y l h) lo hi xs ys

/-- The full filter is reached only after its work charge is reserved. -/
def run (b : Block n g) (lo hi : ℕ) (xs ys : List (StoredEntry n))
    (nx ny budget : ℕ) : BudgetedSeparatorCall.Outcome (BudgetedSeparatorNode.Frame
      (StoredEntry n) (StoredEntry n)) × ℕ :=
  if BudgetedSeparatorNode.charge b.queryBound nx ny ≤ budget then
    let out := prepare b lo hi xs ys
    ((some (out.1.1, budget - BudgetedSeparatorNode.charge b.queryBound nx ny), out.1.2 + 1),
      out.2)
  else ((none, 1), 0)

theorem run_value (b : Block n g) (lo hi : ℕ) (xs ys : List (StoredEntry n))
    (nx ny budget : ℕ) :
    (run b lo hi xs ys nx ny budget).1 =
      BudgetedSeparatorNode.run b.queryBound b.leftQuery b.rightQuery lo hi xs ys nx ny budget := by
  simp only [run, BudgetedSeparatorNode.run, BudgetedSeparatorCall.run]
  split <;> simp_all only [prepare_value]

theorem run_cells (b : Block n g) (lo hi : ℕ) (xs ys : List (StoredEntry n))
    (nx ny budget : ℕ) (hx : xs.length = nx) (hy : ys.length = ny) :
    (run b lo hi xs ys nx ny budget).2 ≤
      8 * (nx + ny + 1) + PreparedCheckerCells.scratch n g := by
  simp only [run]
  split
  · simpa only [hx, hy] using prepare_cells b lo hi xs ys
  · exact Nat.zero_le _

end LowSpaceSubsetSum.StoredNodeCells

end OAI
