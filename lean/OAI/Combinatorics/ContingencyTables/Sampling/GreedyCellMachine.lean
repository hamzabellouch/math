import OAI.Combinatorics.MatchingCount.Machines.TreeListMore
import OAI.Combinatorics.ContingencyTables.Sampling.GreedyFeasibleTable

namespace OAI

/-! # A binary arithmetic machine for one greedy table cell

This is an existing finite tree-machine compiler applied to the actual
minimum/subtraction step. It supplies an executable component for the
feasible-table initializer, rather than an assumed arithmetic oracle.
-/

namespace ContingencyTables.GreedyFeasibleTable

open MatchingFPRAS.TreeTyped

/-- Assigned entry, remaining row margin, and remaining column margin. -/
def cellUpdate (x : ℕ×ℕ) : ℕ×(ℕ×ℕ) :=
  (min x.1 x.2,(x.1-min x.1 x.2,x.2-min x.1 x.2))

/-- A fixed finite program over binary-encoded natural numbers. The
compiler's `correct` field proves its literal execution and step bound. -/
def cellUpdateRealizer : Realizer cellUpdate :=
  (pair minimum (pair
    (composition (pair first minimum) subtract)
    (composition (pair second minimum) subtract))).congr (fun _ => rfl)

lemma cellUpdate_balance (a c : ℕ) :
    (cellUpdate (a,c)).1+(cellUpdate (a,c)).2.1=a ∧
      (cellUpdate (a,c)).1+(cellUpdate (a,c)).2.2=c := by
  simp only [cellUpdate]
  exact ⟨Nat.add_sub_of_le (min_le_left _ _),Nat.add_sub_of_le (min_le_right _ _)⟩

end ContingencyTables.GreedyFeasibleTable

end OAI
