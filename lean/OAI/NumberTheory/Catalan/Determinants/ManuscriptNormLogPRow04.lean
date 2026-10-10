import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup013
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup014
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup015
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup016

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormPRow4_upper :
    manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 4 (0, 0)) ≤
      ((-245704771404397789985869221 / 40000000000000000000000000000) : ℝ) := by
  change (manuscriptNormP4_0Term + (manuscriptNormP4_1Term + (manuscriptNormP4_2Term + (manuscriptNormP4_3Term + (manuscriptNormP4_4Term + (manuscriptNormP4_5Term + (manuscriptNormP4_6Term + (manuscriptNormP4_7Term + (manuscriptNormP4_8Term + (manuscriptNormP4_9Term + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptNormP4_0_enclosure.2, manuscriptNormP4_1_enclosure.2, manuscriptNormP4_2_enclosure.2, manuscriptNormP4_3_enclosure.2, manuscriptNormP4_4_enclosure.2, manuscriptNormP4_5_enclosure.2, manuscriptNormP4_6_enclosure.2, manuscriptNormP4_7_enclosure.2, manuscriptNormP4_8_enclosure.2, manuscriptNormP4_9_enclosure.2]

end InternalCatalan

end

end

end OAI
