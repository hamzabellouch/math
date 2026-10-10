import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup008
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup009
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup010
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup011
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup012

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow2_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 2 (0, 0)) ≤
      ((-10066148211075587538820009047 / 1000000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV2_0Term + (manuscriptNormV2_1Term + (manuscriptNormV2_2Term + (manuscriptNormV2_3Term + (manuscriptNormV2_4Term + (manuscriptNormV2_5Term + (manuscriptNormV2_6Term + (manuscriptNormV2_7Term + (manuscriptNormV2_8Term + (manuscriptNormV2_9Term + (manuscriptNormV2_10Term + (manuscriptNormV2_11Term + (manuscriptNormV2_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV2_0_enclosure.2, manuscriptNormV2_1_enclosure.2, manuscriptNormV2_2_enclosure.2, manuscriptNormV2_3_enclosure.2, manuscriptNormV2_4_enclosure.2, manuscriptNormV2_5_enclosure.2, manuscriptNormV2_6_enclosure.2, manuscriptNormV2_7_enclosure.2, manuscriptNormV2_8_enclosure.2, manuscriptNormV2_9_enclosure.2, manuscriptNormV2_10_enclosure.2, manuscriptNormV2_11_enclosure.2, manuscriptNormV2_12_enclosure.2]

end InternalCatalan

end

end

end OAI
