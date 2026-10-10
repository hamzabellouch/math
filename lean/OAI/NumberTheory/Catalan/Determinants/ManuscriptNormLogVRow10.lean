import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup043
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup044
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup045
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup046
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup047

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow10_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 10 (0, 0)) ≤
      ((-13331960711348427692491383349 / 250000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV10_0Term + (manuscriptNormV10_1Term + (manuscriptNormV10_2Term + (manuscriptNormV10_3Term + (manuscriptNormV10_4Term + (manuscriptNormV10_5Term + (manuscriptNormV10_6Term + (manuscriptNormV10_7Term + (manuscriptNormV10_8Term + (manuscriptNormV10_9Term + (manuscriptNormV10_10Term + (manuscriptNormV10_11Term + (manuscriptNormV10_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV10_0_enclosure.2, manuscriptNormV10_1_enclosure.2, manuscriptNormV10_2_enclosure.2, manuscriptNormV10_3_enclosure.2, manuscriptNormV10_4_enclosure.2, manuscriptNormV10_5_enclosure.2, manuscriptNormV10_6_enclosure.2, manuscriptNormV10_7_enclosure.2, manuscriptNormV10_8_enclosure.2, manuscriptNormV10_9_enclosure.2, manuscriptNormV10_10_enclosure.2, manuscriptNormV10_11_enclosure.2, manuscriptNormV10_12_enclosure.2]

end InternalCatalan

end

end

end OAI
