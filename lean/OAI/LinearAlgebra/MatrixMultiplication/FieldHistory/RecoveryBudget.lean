import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.MaskCore
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InverseLinearRecovery

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRecovery

open AllFieldHistory AllFieldHistorySupport

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def minimumDilation (allocation : Allocation) (ε : ℝ) : ℕ :=
  Nat.ceil (3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6)) + 2

theorem minimumDilation_spec (allocation : Allocation) (ε : ℝ) {m : ℕ}
    (hm : minimumDilation (K := K) (tick := tick) allocation ε ≤ m) :
    2 ≤ m ∧
      3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6) <
        (m : ℝ) := by
  constructor
  · exact (Nat.le_add_left 2 _).trans hm
  · have hc := Nat.le_ceil
      (3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6))
    have hm' : (Nat.ceil
        (3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6)) : ℝ) + 2 ≤ m := by
      exact_mod_cast hm
    linarith

def shiftCount (allocation : Allocation) (ε : ℝ) (m : ℕ) : ℕ :=
  RecoveryGrowth.shiftCount (supportRate (K := K) (tick := tick) allocation)
    (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6) m

theorem replication_subexponential (allocation : Allocation) (ε : ℝ) :
    Filter.Tendsto (fun m : ℕ =>
      Real.log (Fintype.card (InverseLinearRecovery.MaskRectangles
        (shiftCount (K := K) (tick := tick) allocation ε m))) / m)
      Filter.atTop (nhds 0) :=
  InverseLinearRecovery.subexponential_copies (supportRate_pos allocation)
    (by have := AllFieldHistoryMasks.lossConstant_nonneg (K := K) (tick := tick) allocation ε
        linarith)

end MatrixMultiplication.AllFieldHistoryRecovery

end

end OAI
