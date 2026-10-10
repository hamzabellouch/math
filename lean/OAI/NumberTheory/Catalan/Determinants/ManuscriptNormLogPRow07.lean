import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup023
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup024
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup025
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup026

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormPRow7_upper :
    manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 7 (0, 0)) ≤
      ((-2248149022781123755876138879 / 500000000000000000000000000000) : ℝ) := by
  change (manuscriptNormP7_0Term + (manuscriptNormP7_1Term + (manuscriptNormP7_2Term + (manuscriptNormP7_3Term + (manuscriptNormP7_4Term + (manuscriptNormP7_5Term + (manuscriptNormP7_6Term + (manuscriptNormP7_7Term + (manuscriptNormP7_8Term + (manuscriptNormP7_9Term + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptNormP7_0_enclosure.2, manuscriptNormP7_1_enclosure.2, manuscriptNormP7_2_enclosure.2, manuscriptNormP7_3_enclosure.2, manuscriptNormP7_4_enclosure.2, manuscriptNormP7_5_enclosure.2, manuscriptNormP7_6_enclosure.2, manuscriptNormP7_7_enclosure.2, manuscriptNormP7_8_enclosure.2, manuscriptNormP7_9_enclosure.2]

end InternalCatalan

end

end

end OAI
