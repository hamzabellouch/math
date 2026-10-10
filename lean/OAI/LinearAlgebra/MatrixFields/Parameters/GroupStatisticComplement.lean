import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.GroupOrbitTransport

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldGroupStatisticComplement

open AllFieldHistory AllFieldHistoryChildLaws

theorem statistic_wordComplement {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (w : Fin (activeHalfLength h.val) → Fin 7) :
    statistic h.val (CWCompatibilityTransfer.wordComplement w) =
      AllFieldGroupOrbitData.complement h (statistic h.val w) := by
  rcases h with ⟨⟨⟨work, phi⟩, ht⟩, ho⟩
  cases work with
  | stageA a => exact CWCompleteStatistics.four_complement w
  | stageB b => exact CWCompleteStatistics.two_complement w
  | stageC c => rfl

end MatrixMultiplication.AllFieldGroupStatisticComplement

end

end MatrixAllFields

end OAI
