import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup000
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup001
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup002
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup003
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup004

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow0_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 0 (0, 0)) ≤
      ((101569623279045545348570517459 / 1000000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV0_0Term + (manuscriptNormV0_1Term + (manuscriptNormV0_2Term + (manuscriptNormV0_3Term + (manuscriptNormV0_4Term + (manuscriptNormV0_5Term + (manuscriptNormV0_6Term + (manuscriptNormV0_7Term + (manuscriptNormV0_8Term + (manuscriptNormV0_9Term + (manuscriptNormV0_10Term + (manuscriptNormV0_11Term + (manuscriptNormV0_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV0_0_enclosure.2, manuscriptNormV0_1_enclosure.2, manuscriptNormV0_2_enclosure.2, manuscriptNormV0_3_enclosure.2, manuscriptNormV0_4_enclosure.2, manuscriptNormV0_5_enclosure.2, manuscriptNormV0_6_enclosure.2, manuscriptNormV0_7_enclosure.2, manuscriptNormV0_8_enclosure.2, manuscriptNormV0_9_enclosure.2, manuscriptNormV0_10_enclosure.2, manuscriptNormV0_11_enclosure.2, manuscriptNormV0_12_enclosure.2]

end InternalCatalan

end

end

end OAI
