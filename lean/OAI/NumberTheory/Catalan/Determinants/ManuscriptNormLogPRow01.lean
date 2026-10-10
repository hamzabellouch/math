import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup003
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup004
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup005
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup006

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormPRow1_upper :
    manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 1 (0, 0)) ≤
      ((4239937178462756377151314421 / 1000000000000000000000000000000) : ℝ) := by
  change (manuscriptNormP1_0Term + (manuscriptNormP1_1Term + (manuscriptNormP1_2Term + (manuscriptNormP1_3Term + (manuscriptNormP1_4Term + (manuscriptNormP1_5Term + (manuscriptNormP1_6Term + (manuscriptNormP1_7Term + (manuscriptNormP1_8Term + (manuscriptNormP1_9Term + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptNormP1_0_enclosure.2, manuscriptNormP1_1_enclosure.2, manuscriptNormP1_2_enclosure.2, manuscriptNormP1_3_enclosure.2, manuscriptNormP1_4_enclosure.2, manuscriptNormP1_5_enclosure.2, manuscriptNormP1_6_enclosure.2, manuscriptNormP1_7_enclosure.2, manuscriptNormP1_8_enclosure.2, manuscriptNormP1_9_enclosure.2]

end InternalCatalan

end

end

end OAI
