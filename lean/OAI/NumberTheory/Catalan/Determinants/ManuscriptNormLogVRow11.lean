import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup047
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup048
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup049
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup050
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup051

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow11_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 11 (0, 0)) ≤
      ((59495018237695265878229151011 / 500000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV11_0Term + (manuscriptNormV11_1Term + (manuscriptNormV11_2Term + (manuscriptNormV11_3Term + (manuscriptNormV11_4Term + (manuscriptNormV11_5Term + (manuscriptNormV11_6Term + (manuscriptNormV11_7Term + (manuscriptNormV11_8Term + (manuscriptNormV11_9Term + (manuscriptNormV11_10Term + (manuscriptNormV11_11Term + (manuscriptNormV11_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV11_0_enclosure.2, manuscriptNormV11_1_enclosure.2, manuscriptNormV11_2_enclosure.2, manuscriptNormV11_3_enclosure.2, manuscriptNormV11_4_enclosure.2, manuscriptNormV11_5_enclosure.2, manuscriptNormV11_6_enclosure.2, manuscriptNormV11_7_enclosure.2, manuscriptNormV11_8_enclosure.2, manuscriptNormV11_9_enclosure.2, manuscriptNormV11_10_enclosure.2, manuscriptNormV11_11_enclosure.2, manuscriptNormV11_12_enclosure.2]

end InternalCatalan

end

end

end OAI
