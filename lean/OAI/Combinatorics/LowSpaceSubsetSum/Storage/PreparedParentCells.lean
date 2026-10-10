import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationJoinCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPreparedParent

namespace OAI

/-! # Prepared contexts throughout the stopped parent collection

Both actual immutable right arrays remain shared during collection. After
the join, projection retains only its safe dictionary and scalar counters.
The setup routines are accounted for by their own live-cell traces.
-/

namespace LowSpaceSubsetSum.PreparedParentCells

variable {n : ℕ}

def runContexts (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (fuel₀ fuel₁ control : ℕ)
    (left : PreparedReaderContext.Context I F P .direct)
    (right : PreparedReaderContext.Context I F P (.complementary t)) (budget : ℕ) :=
  let out := RepresentationJoinCells.withArrays I F P t C B #[] left.right #[] right.right
    fuel₀ fuel₁ control left.state right.state budget
  ((out.1.1.map (fun (value, remaining) => (PreparedParentExecution.project value, remaining)), out.1.2),
    out.2 + 32)

theorem runContexts_value (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (fuel₀ fuel₁ control : ℕ)
    (left : PreparedReaderContext.Context I F P .direct)
    (right : PreparedReaderContext.Context I F P (.complementary t)) (budget : ℕ) :
    (runContexts I F P t C B fuel₀ fuel₁ control left right budget).1 =
      BudgetedPreparedParent.runContexts I F P t C B fuel₀ fuel₁ control left right budget := by
  simp only [runContexts, RepresentationJoinCells.withArrays, RepresentationJoinCells.parent_value,
    BudgetedPreparedParent.runContexts]

theorem runContexts_cells (I : Instance n) (F : IndexedMask n) (P t : ℤ) (C B : ℕ)
    (fuel₀ fuel₁ control : ℕ)
    (left : PreparedReaderContext.Context I F P .direct)
    (right : PreparedReaderContext.Context I F P (.complementary t)) (budget : ℕ)
    (hn : 10000 ≤ n) (hd₀ : left.depth ≤ n) (hd₁ : right.depth ≤ n)
    (ht₀ : 2 ^ (left.depth + 1) ≤ 4 * (C + 1))
    (ht₁ : 2 ^ (right.depth + 1) ≤ 4 * (C + 1))
    (hl : left.right.size ≤ C) (hr : right.right.size ≤ C) (hB : B ≤ C) :
    (runContexts I F P t C B fuel₀ fuel₁ control left right budget).2 ≤
      inputScale I ^ 13 * (C + 1) := by
  have h := RepresentationJoinCells.withArrays_cells I F P t C B #[] left.right #[] right.right
    fuel₀ fuel₁ control left.state right.state budget hn hd₀ hd₁ ht₀ ht₁ hB
    (by simp) hl (by simp) hr
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hp : 32 ≤ inputScale I ^ 12 := by
    have h : inputScale I ≤ inputScale I ^ 12 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ inputScale I) (by decide : 1 ≤ 12)
    omega
  have hm : 2 * inputScale I ^ 12 ≤ inputScale I ^ 13 := by
    calc
      _ ≤ inputScale I * inputScale I ^ 12 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hb := Nat.mul_le_mul_right (C + 1) hm
  change _ + 32 ≤ _
  nlinarith only [h, hp, hb]

end LowSpaceSubsetSum.PreparedParentCells

end OAI
