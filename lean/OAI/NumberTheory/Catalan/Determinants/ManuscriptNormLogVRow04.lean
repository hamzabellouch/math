import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup017
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup018
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup019
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup020
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup021

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow4_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 4 (0, 0)) ≤
      ((-17788016786043582944131371579 / 500000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV4_0Term + (manuscriptNormV4_1Term + (manuscriptNormV4_2Term + (manuscriptNormV4_3Term + (manuscriptNormV4_4Term + (manuscriptNormV4_5Term + (manuscriptNormV4_6Term + (manuscriptNormV4_7Term + (manuscriptNormV4_8Term + (manuscriptNormV4_9Term + (manuscriptNormV4_10Term + (manuscriptNormV4_11Term + (manuscriptNormV4_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV4_0_enclosure.2, manuscriptNormV4_1_enclosure.2, manuscriptNormV4_2_enclosure.2, manuscriptNormV4_3_enclosure.2, manuscriptNormV4_4_enclosure.2, manuscriptNormV4_5_enclosure.2, manuscriptNormV4_6_enclosure.2, manuscriptNormV4_7_enclosure.2, manuscriptNormV4_8_enclosure.2, manuscriptNormV4_9_enclosure.2, manuscriptNormV4_10_enclosure.2, manuscriptNormV4_11_enclosure.2, manuscriptNormV4_12_enclosure.2]

end InternalCatalan

end

end

end OAI
