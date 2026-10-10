import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup021
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup022
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup023
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup024
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup025

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow5_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 5 (0, 0)) ≤
      ((117406663890248020465524666789 / 1000000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV5_0Term + (manuscriptNormV5_1Term + (manuscriptNormV5_2Term + (manuscriptNormV5_3Term + (manuscriptNormV5_4Term + (manuscriptNormV5_5Term + (manuscriptNormV5_6Term + (manuscriptNormV5_7Term + (manuscriptNormV5_8Term + (manuscriptNormV5_9Term + (manuscriptNormV5_10Term + (manuscriptNormV5_11Term + (manuscriptNormV5_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV5_0_enclosure.2, manuscriptNormV5_1_enclosure.2, manuscriptNormV5_2_enclosure.2, manuscriptNormV5_3_enclosure.2, manuscriptNormV5_4_enclosure.2, manuscriptNormV5_5_enclosure.2, manuscriptNormV5_6_enclosure.2, manuscriptNormV5_7_enclosure.2, manuscriptNormV5_8_enclosure.2, manuscriptNormV5_9_enclosure.2, manuscriptNormV5_10_enclosure.2, manuscriptNormV5_11_enclosure.2, manuscriptNormV5_12_enclosure.2]

end InternalCatalan

end

end

end OAI
