import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup019
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup020
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup021
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup022

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormPRow6_upper :
    manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 6 (0, 0)) ≤
      ((-281018627847640469871664967 / 62500000000000000000000000000) : ℝ) := by
  change (manuscriptNormP6_0Term + (manuscriptNormP6_1Term + (manuscriptNormP6_2Term + (manuscriptNormP6_3Term + (manuscriptNormP6_4Term + (manuscriptNormP6_5Term + (manuscriptNormP6_6Term + (manuscriptNormP6_7Term + (manuscriptNormP6_8Term + (manuscriptNormP6_9Term + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptNormP6_0_enclosure.2, manuscriptNormP6_1_enclosure.2, manuscriptNormP6_2_enclosure.2, manuscriptNormP6_3_enclosure.2, manuscriptNormP6_4_enclosure.2, manuscriptNormP6_5_enclosure.2, manuscriptNormP6_6_enclosure.2, manuscriptNormP6_7_enclosure.2, manuscriptNormP6_8_enclosure.2, manuscriptNormP6_9_enclosure.2]

end InternalCatalan

end

end

end OAI
