import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineRangeSpace
import OAI.Combinatorics.EditApproximation.Binary.BitQuerySpace
import OAI.Combinatorics.EditApproximation.Binary.BitQueryNormalize
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem powerDenominatorAllocation_le_work (a : BinaryFraction) (base : List Bool)
    (hbase : 0 < bitWordValue base) (n : ℕ) :
    powerDenominatorAllocation a base hbase n ≤ (powerDenominatorWithWork a base hbase n).2 := by
  have hp := bitPowerAllocation_le_work base n
  have hf := fixedDenominatorAllocation_le_work a (bitPowerWithWork base n).1
    (by rw [bitPowerWithWork_value]; exact Nat.pow_pos hbase)
  unfold powerDenominatorAllocation powerDenominatorWithWork
  dsimp only
  omega



theorem finishCachedAllocation_le_work (raw : BinaryFraction × ℕ) (allocation : ℕ)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ) (ha : allocation ≤ raw.2) :
    finishCachedAllocation raw allocation base hbase remaining ≤ (finishCachedWithWork raw base hbase remaining).2 := by
  have hp := powerDenominatorAllocation_le_work raw.1 base hbase remaining
  unfold finishCachedAllocation finishCachedWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

namespace EditApproximation.BitQuery.Heap

def normalize {ι : Type*} {program : BitQuery ι BinaryFraction} (heap : Heap program)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ) :
    Heap (program.normalize base hbase remaining) :=
  heap.bind _ fun word => computeOf (BinaryFraction.finishCachedWithWork (word, 0) base hbase remaining)
    (BinaryFraction.finishCachedAllocation (word, 0) 0 base hbase remaining)
    (BinaryFraction.finishCachedAllocation_le_work (word, 0) 0 base hbase remaining le_rfl)

end EditApproximation.BitQuery.Heap

end OAI
