import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup029
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup030
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup031
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogPGroup032

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormPRow9_upper :
    manuscriptNormLogRow barrierP2Tail (barrierP2Tail.getD 9 (0, 0)) ≤
      ((8601200440115989850300210127 / 500000000000000000000000000000) : ℝ) := by
  change (manuscriptNormP9_0Term + (manuscriptNormP9_1Term + (manuscriptNormP9_2Term + (manuscriptNormP9_3Term + (manuscriptNormP9_4Term + (manuscriptNormP9_5Term + (manuscriptNormP9_6Term + (manuscriptNormP9_7Term + (manuscriptNormP9_8Term + (manuscriptNormP9_9Term + (0 : ℝ))))))))))) ≤ _
  linarith only [manuscriptNormP9_0_enclosure.2, manuscriptNormP9_1_enclosure.2, manuscriptNormP9_2_enclosure.2, manuscriptNormP9_3_enclosure.2, manuscriptNormP9_4_enclosure.2, manuscriptNormP9_5_enclosure.2, manuscriptNormP9_6_enclosure.2, manuscriptNormP9_7_enclosure.2, manuscriptNormP9_8_enclosure.2, manuscriptNormP9_9_enclosure.2]

end InternalCatalan

end

end

end OAI
