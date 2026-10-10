import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup009
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup010
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup011
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup012

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormPRow3_upper :
    manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 3 (0, 0)) ≤
      ((64937392547326962796226760577 / 1000000000000000000000000000000) : ℝ) := by
  change (manuscriptNormP3_0Term + (manuscriptNormP3_1Term + (manuscriptNormP3_2Term + (manuscriptNormP3_3Term + (manuscriptNormP3_4Term + (manuscriptNormP3_5Term + (manuscriptNormP3_6Term + (manuscriptNormP3_7Term + (manuscriptNormP3_8Term + (manuscriptNormP3_9Term + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptNormP3_0_enclosure.2, manuscriptNormP3_1_enclosure.2, manuscriptNormP3_2_enclosure.2, manuscriptNormP3_3_enclosure.2, manuscriptNormP3_4_enclosure.2, manuscriptNormP3_5_enclosure.2, manuscriptNormP3_6_enclosure.2, manuscriptNormP3_7_enclosure.2, manuscriptNormP3_8_enclosure.2, manuscriptNormP3_9_enclosure.2]

end InternalCatalan

end

end

end OAI
