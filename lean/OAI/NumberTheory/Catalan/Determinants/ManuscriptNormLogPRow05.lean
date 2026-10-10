import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup016
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup017
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup018
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup019

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormPRow5_upper :
    manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 5 (0, 0)) ≤
      ((-307130964255497237530195231 / 50000000000000000000000000000) : ℝ) := by
  change (manuscriptNormP5_0Term + (manuscriptNormP5_1Term + (manuscriptNormP5_2Term + (manuscriptNormP5_3Term + (manuscriptNormP5_4Term + (manuscriptNormP5_5Term + (manuscriptNormP5_6Term + (manuscriptNormP5_7Term + (manuscriptNormP5_8Term + (manuscriptNormP5_9Term + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptNormP5_0_enclosure.2, manuscriptNormP5_1_enclosure.2, manuscriptNormP5_2_enclosure.2, manuscriptNormP5_3_enclosure.2, manuscriptNormP5_4_enclosure.2, manuscriptNormP5_5_enclosure.2, manuscriptNormP5_6_enclosure.2, manuscriptNormP5_7_enclosure.2, manuscriptNormP5_8_enclosure.2, manuscriptNormP5_9_enclosure.2]

end InternalCatalan

end

end

end OAI
