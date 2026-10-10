import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedResidueLoop
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorCells

namespace OAI

/-! # A single live workspace throughout the residue counter loop -/

namespace LowSpaceSubsetSum.ResidueLoopCells

open BudgetedSeparatorCells

def loop (bucket : ℕ → ℕ → Execution Bool) :
    ℕ → ℕ → ℕ → ℕ → ℕ → Execution Bool
  | z, remaining, budget, work, peak =>
    if 4 ≤ budget then
      match remaining with
      | 0 => ((some (false, budget - 4), work + 1), max peak 16)
      | remaining + 1 =>
        let out := bucket z (budget - 4)
        let p := max peak (out.2 + 16)
        match out.1.1 with
        | none => ((none, work + out.1.2 + 2), p)
        | some (true, left) => ((some (true, left), work + out.1.2 + 3), p)
        | some (false, left) => loop bucket (z + 1) remaining left (work + out.1.2 + 3) p
    else ((none, work + 1), max peak 16)

def run (bucket : ℕ → ℕ → Execution Bool) (z remaining budget : ℕ) : Execution Bool :=
  loop bucket z remaining budget 0 16

theorem loop_value (bucket : ℕ → ℕ → Execution Bool) (z remaining budget work peak : ℕ) :
    (loop bucket z remaining budget work peak).1 =
      BudgetedResidueLoop.loop (fun z b => (bucket z b).1) z remaining budget work := by
  induction remaining generalizing z budget work peak with
  | zero => simp only [loop, BudgetedResidueLoop.loop]; split <;> rfl
  | succ remaining ih =>
    simp only [loop, BudgetedResidueLoop.loop]
    split
    · split
      · simp_all only
      · simp_all only
      · simp_all only
    · rfl

theorem value (bucket : ℕ → ℕ → Execution Bool) (z remaining budget : ℕ) :
    (run bucket z remaining budget).1 =
      BudgetedResidueLoop.run (fun z b => (bucket z b).1) z remaining budget :=
  loop_value bucket z remaining budget 0 16

theorem loop_cells (bucket : ℕ → ℕ → Execution Bool) (L : ℕ)
    (hbucket : ∀ z b, (bucket z b).2 ≤ L) (z remaining budget work peak : ℕ)
    (hpeak : peak ≤ L + 16) :
    (loop bucket z remaining budget work peak).2 ≤ L + 16 := by
  induction remaining generalizing z budget work peak with
  | zero => simp only [loop]; split <;> exact max_le hpeak (by omega)
  | succ remaining ih =>
    have hb := hbucket z (budget-4)
    have hp : max peak ((bucket z (budget-4)).2+16) ≤ L+16 :=
      max_le hpeak (Nat.add_le_add_right hb 16)
    simp only [loop]
    split
    · split
      · exact hp
      · exact hp
      · exact ih _ _ _ _ hp
    · exact max_le hpeak (by omega)

theorem cells (bucket : ℕ → ℕ → Execution Bool) (L : ℕ)
    (hbucket : ∀ z b, (bucket z b).2 ≤ L) (z remaining budget : ℕ) :
    (run bucket z remaining budget).2 ≤ L + 16 :=
  loop_cells bucket L hbucket z remaining budget 0 16 (by omega)

end LowSpaceSubsetSum.ResidueLoopCells

end OAI
