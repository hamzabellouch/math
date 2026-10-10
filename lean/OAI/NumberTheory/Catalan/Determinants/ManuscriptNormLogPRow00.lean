import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup001
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup002

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormPRow0_upper :
    manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 0 (0, 0)) ≤
      ((778974678889387440646188819 / 50000000000000000000000000000) : ℝ) := by
  change (manuscriptP00NormLogTerm + (manuscriptNormP0_1Term + (manuscriptNormP0_2Term + (manuscriptNormP0_3Term + (manuscriptNormP0_4Term + (manuscriptNormP0_5Term + (manuscriptNormP0_6Term + (manuscriptNormP0_7Term + (manuscriptNormP0_8Term + (manuscriptNormP0_9Term + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptP00_norm_log_enclosure.2, manuscriptNormP0_1_enclosure.2, manuscriptNormP0_2_enclosure.2, manuscriptNormP0_3_enclosure.2, manuscriptNormP0_4_enclosure.2, manuscriptNormP0_5_enclosure.2, manuscriptNormP0_6_enclosure.2, manuscriptNormP0_7_enclosure.2, manuscriptNormP0_8_enclosure.2, manuscriptNormP0_9_enclosure.2]

end InternalCatalan

end

end

end OAI
