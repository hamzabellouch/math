import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.ProducedMaskCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.MaskCore

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryProducedMasks

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldHistoryMasks InheritedMasks
open JointCanonicalization
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem childWindows_of_produced_masks (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h)) :
    AllFieldHistoryMasks.childWindows allocation dilation ε side
      (regroupWords allocation dilation x) :=
  canonicalWindows_of_produced_masks allocation dilation hε side x hx

end MatrixMultiplication.AllFieldHistoryProducedMasks

end

end OAI
