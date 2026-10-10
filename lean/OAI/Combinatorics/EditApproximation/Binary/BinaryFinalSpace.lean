import OAI.Combinatorics.EditApproximation.Binary.BinaryFinalAnswer
import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialGuardSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem finalAnswerAllocation_le_work (N : ℕ) (a : BinaryFraction) :
    finalAnswerAllocation N a ≤ (finalAnswerWithWork N a).2 := by
  have hf := naturalFloorAllocation_le_work a
  have hm := naturalWordLEAllocation_le_work N.bits (naturalFloorWithWork a).1
  unfold finalAnswerAllocation finalAnswerWithWork wordMinWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
