import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup052
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup053
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup054
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup055

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow12_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 12 (0, 0)) ≤
      ((59495018237695265878229151011 / 500000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV12_0Term + (manuscriptNormV12_1Term + (manuscriptNormV12_2Term + (manuscriptNormV12_3Term + (manuscriptNormV12_4Term + (manuscriptNormV12_5Term + (manuscriptNormV12_6Term + (manuscriptNormV12_7Term + (manuscriptNormV12_8Term + (manuscriptNormV12_9Term + (manuscriptNormV12_10Term + (manuscriptNormV12_11Term + (manuscriptNormV12_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV12_0_enclosure.2, manuscriptNormV12_1_enclosure.2, manuscriptNormV12_2_enclosure.2, manuscriptNormV12_3_enclosure.2, manuscriptNormV12_4_enclosure.2, manuscriptNormV12_5_enclosure.2, manuscriptNormV12_6_enclosure.2, manuscriptNormV12_7_enclosure.2, manuscriptNormV12_8_enclosure.2, manuscriptNormV12_9_enclosure.2, manuscriptNormV12_10_enclosure.2, manuscriptNormV12_11_enclosure.2, manuscriptNormV12_12_enclosure.2]

end InternalCatalan

end

end

end OAI
