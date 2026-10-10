import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup013
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup014
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup015
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup016
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup017

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow3_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 3 (0, 0)) ≤
      ((8892604089276253133653642727 / 500000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV3_0Term + (manuscriptNormV3_1Term + (manuscriptNormV3_2Term + (manuscriptNormV3_3Term + (manuscriptNormV3_4Term + (manuscriptNormV3_5Term + (manuscriptNormV3_6Term + (manuscriptNormV3_7Term + (manuscriptNormV3_8Term + (manuscriptNormV3_9Term + (manuscriptNormV3_10Term + (manuscriptNormV3_11Term + (manuscriptNormV3_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV3_0_enclosure.2, manuscriptNormV3_1_enclosure.2, manuscriptNormV3_2_enclosure.2, manuscriptNormV3_3_enclosure.2, manuscriptNormV3_4_enclosure.2, manuscriptNormV3_5_enclosure.2, manuscriptNormV3_6_enclosure.2, manuscriptNormV3_7_enclosure.2, manuscriptNormV3_8_enclosure.2, manuscriptNormV3_9_enclosure.2, manuscriptNormV3_10_enclosure.2, manuscriptNormV3_11_enclosure.2, manuscriptNormV3_12_enclosure.2]

end InternalCatalan

end

end

end OAI
