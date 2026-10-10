import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup026
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup027
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup028
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup029
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup030

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow6_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 6 (0, 0)) ≤
      ((117406663890248020465524666789 / 1000000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV6_0Term + (manuscriptNormV6_1Term + (manuscriptNormV6_2Term + (manuscriptNormV6_3Term + (manuscriptNormV6_4Term + (manuscriptNormV6_5Term + (manuscriptNormV6_6Term + (manuscriptNormV6_7Term + (manuscriptNormV6_8Term + (manuscriptNormV6_9Term + (manuscriptNormV6_10Term + (manuscriptNormV6_11Term + (manuscriptNormV6_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV6_0_enclosure.2, manuscriptNormV6_1_enclosure.2, manuscriptNormV6_2_enclosure.2, manuscriptNormV6_3_enclosure.2, manuscriptNormV6_4_enclosure.2, manuscriptNormV6_5_enclosure.2, manuscriptNormV6_6_enclosure.2, manuscriptNormV6_7_enclosure.2, manuscriptNormV6_8_enclosure.2, manuscriptNormV6_9_enclosure.2, manuscriptNormV6_10_enclosure.2, manuscriptNormV6_11_enclosure.2, manuscriptNormV6_12_enclosure.2]

end InternalCatalan

end

end

end OAI
