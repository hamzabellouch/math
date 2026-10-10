import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup006
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup007
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup008
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup009

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormPRow2_upper :
    manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 2 (0, 0)) ≤
      ((64937392547326962796226760577 / 1000000000000000000000000000000) : ℝ) := by
  change (manuscriptNormP2_0Term + (manuscriptNormP2_1Term + (manuscriptNormP2_2Term + (manuscriptNormP2_3Term + (manuscriptNormP2_4Term + (manuscriptNormP2_5Term + (manuscriptNormP2_6Term + (manuscriptNormP2_7Term + (manuscriptNormP2_8Term + (manuscriptNormP2_9Term + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptNormP2_0_enclosure.2, manuscriptNormP2_1_enclosure.2, manuscriptNormP2_2_enclosure.2, manuscriptNormP2_3_enclosure.2, manuscriptNormP2_4_enclosure.2, manuscriptNormP2_5_enclosure.2, manuscriptNormP2_6_enclosure.2, manuscriptNormP2_7_enclosure.2, manuscriptNormP2_8_enclosure.2, manuscriptNormP2_9_enclosure.2]

end InternalCatalan

end

end

end OAI
