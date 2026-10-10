import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitData
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWCompatibilityTransfer

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

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

end OAI
