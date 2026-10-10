import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredFilterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorNode

namespace OAI

/-! # The prepaid filter node realizes its local cell allowance -/

namespace LowSpaceSubsetSum.BudgetedNodeCells

variable {α β : Type*}

def prepare (test₁ : α → ℕ → ℕ → (Bool × ℕ) × ℕ)
    (test₂ : β → ℕ → ℕ → (Bool × ℕ) × ℕ)
    (lo hi : ℕ) (xs : List α) (ys : List β) :
    (BudgetedSeparatorNode.Frame α β × ℕ) × ℕ :=
  let a := MeasuredFilterCells.run (fun x => test₁ x lo hi) xs
  let b := MeasuredFilterCells.run (fun y => test₂ y lo hi) ys
  let nx := a.1.1.length
  let ny := b.1.1.length
  ((⟨a.1.1, b.1.1, nx, ny, rfl, rfl⟩, a.1.2 + b.1.2 + 2 * (nx + ny) + 12),
    xs.length + ys.length + 4 + max a.2 (nx + b.2))

theorem prepare_value (test₁ : α → ℕ → ℕ → (Bool × ℕ) × ℕ)
    (test₂ : β → ℕ → ℕ → (Bool × ℕ) × ℕ)
    (lo hi : ℕ) (xs : List α) (ys : List β) :
    (prepare test₁ test₂ lo hi xs ys).1 =
      BudgetedSeparatorNode.prepare (fun x l h => (test₁ x l h).1)
        (fun y l h => (test₂ y l h).1) lo hi xs ys := by
  simp only [prepare, MeasuredFilterCells.run_value, BudgetedSeparatorNode.prepare,
    MeasuredSeparatorTraversal.keep]

theorem prepare_cells (test₁ : α → ℕ → ℕ → (Bool × ℕ) × ℕ)
    (test₂ : β → ℕ → ℕ → (Bool × ℕ) × ℕ) (H : ℕ)
    (h₁ : ∀ x l h, (test₁ x l h).2 ≤ H) (h₂ : ∀ y l h, (test₂ y l h).2 ≤ H)
    (lo hi : ℕ) (xs : List α) (ys : List β) :
    (prepare test₁ test₂ lo hi xs ys).2 ≤ 8 * (xs.length + ys.length + 1) + H := by
  have ha := MeasuredFilterCells.run_cells (fun x => test₁ x lo hi) H (fun x => h₁ x lo hi) xs
  have hb := MeasuredFilterCells.run_cells (fun y => test₂ y lo hi) H (fun y => h₂ y lo hi) ys
  have hl := MeasuredFilterCells.run_length (fun x => test₁ x lo hi) xs
  have ha' := ha.trans (show 2 * xs.length + H + 4 ≤
    2 * (xs.length + ys.length) + H + 4 by omega)
  have hb' : (MeasuredFilterCells.run (fun x => test₁ x lo hi) xs).1.1.length +
      (MeasuredFilterCells.run (fun y => test₂ y lo hi) ys).2 ≤
      2 * (xs.length + ys.length) + H + 4 := by omega
  have hm := max_le ha' hb'
  change xs.length + ys.length + 4 + max _ _ ≤ _
  omega

end LowSpaceSubsetSum.BudgetedNodeCells

end OAI
