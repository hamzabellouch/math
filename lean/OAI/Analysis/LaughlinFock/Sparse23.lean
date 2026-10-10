import Mathlib
import OAI.Analysis.LaughlinFock.SparseTrace

namespace OAI

/-! Sparse23. -/
namespace LaughlinFock

def collectedFourData_23_0 : List CollectedFourTerm := [
  ⟨7, 8, 8, 7, 8, 8, 41366159586883379063399822680236494698001203200000000000⟩
]

def collectedFourData_23 : List CollectedFourTerm := collectedFourData_23_0

theorem collectedFourChecked_23 : collectedFourTerms 23 = collectedFourData_23 := by
  decide +kernel

end LaughlinFock

end OAI
