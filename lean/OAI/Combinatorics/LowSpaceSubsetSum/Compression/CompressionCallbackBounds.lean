import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionCallbackCells

namespace OAI

/-! # Capacity-scaled bounds for the actual compression callbacks -/

namespace LowSpaceSubsetSum.CompressionCallbackBounds

variable {n : ℕ}

private theorem polynomial (I : Instance n) (hn : 10000 ≤ n) :
    1000*(inputScale I+1) ≤ inputScale I^4 := by
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have h2 : 1000*(inputScale I+1) ≤ inputScale I^2 := by nlinarith only [hu]
  exact h2.trans (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 4))

theorem dictionary (I : Instance n) (hn : 10000 ≤ n) (C : ℕ)
    (r : CompressionCallbacks.Dictionary I C) :
    CompressionCallbackCells.dictionaryCells r ≤ inputScale I^4*(C+1) := by
  have h := CompressionCallbackCells.dictionaryCells_bound I C r
  have hp := Nat.mul_le_mul_right (C+1) (polynomial I hn)
  nlinarith only [h,hp]

theorem report (I : Instance n) (hn : 10000 ≤ n) (C : ℕ) (x y : ℤ)
    (r : CompressionCallbacks.Dictionary I C) :
    (CompressionCallbackCells.report I C x y r).2 ≤ inputScale I^4*(C+1) := by
  have h := CompressionCallbackCells.report_cells I C x y r
  have hp := Nat.mul_le_mul_right (C+1) (polynomial I hn)
  nlinarith only [h,hp]

theorem probe (I : Instance n) (hn : 10000 ≤ n) (C : ℕ)
    (tree : BinaryTrie.Tree) (t x y : ℤ) (found : Bool) :
    (CompressionCallbackCells.probe I tree t x y found).2 ≤ inputScale I^4*(C+1) := by
  have h := CompressionCallbackCells.probe_cells I tree t x y found
  have hp := Nat.mul_le_mul_right (C+1) (polynomial I hn)
  nlinarith only [h,hp]

end LowSpaceSubsetSum.CompressionCallbackBounds

end OAI
