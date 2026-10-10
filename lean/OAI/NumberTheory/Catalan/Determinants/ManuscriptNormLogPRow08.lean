import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup026
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup027
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup028
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup029

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormPRow8_upper :
    manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 8 (0, 0)) ≤
      ((17202400880231979705837607873 / 1000000000000000000000000000000) : ℝ) := by
  change (manuscriptNormP8_0Term + (manuscriptNormP8_1Term + (manuscriptNormP8_2Term + (manuscriptNormP8_3Term + (manuscriptNormP8_4Term + (manuscriptNormP8_5Term + (manuscriptNormP8_6Term + (manuscriptNormP8_7Term + (manuscriptNormP8_8Term + (manuscriptNormP8_9Term + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptNormP8_0_enclosure.2, manuscriptNormP8_1_enclosure.2, manuscriptNormP8_2_enclosure.2, manuscriptNormP8_3_enclosure.2, manuscriptNormP8_4_enclosure.2, manuscriptNormP8_5_enclosure.2, manuscriptNormP8_6_enclosure.2, manuscriptNormP8_7_enclosure.2, manuscriptNormP8_8_enclosure.2, manuscriptNormP8_9_enclosure.2]

end InternalCatalan

end

end

end OAI
