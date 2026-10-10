import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup004
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup005
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup006
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup007
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup008

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow1_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 1 (0, 0)) ≤
      ((9497051844214097750258868783 / 250000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV1_0Term + (manuscriptNormV1_1Term + (manuscriptNormV1_2Term + (manuscriptNormV1_3Term + (manuscriptNormV1_4Term + (manuscriptNormV1_5Term + (manuscriptNormV1_6Term + (manuscriptNormV1_7Term + (manuscriptNormV1_8Term + (manuscriptNormV1_9Term + (manuscriptNormV1_10Term + (manuscriptNormV1_11Term + (manuscriptNormV1_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV1_0_enclosure.2, manuscriptNormV1_1_enclosure.2, manuscriptNormV1_2_enclosure.2, manuscriptNormV1_3_enclosure.2, manuscriptNormV1_4_enclosure.2, manuscriptNormV1_5_enclosure.2, manuscriptNormV1_6_enclosure.2, manuscriptNormV1_7_enclosure.2, manuscriptNormV1_8_enclosure.2, manuscriptNormV1_9_enclosure.2, manuscriptNormV1_10_enclosure.2, manuscriptNormV1_11_enclosure.2, manuscriptNormV1_12_enclosure.2]

end InternalCatalan

end

end

end OAI
