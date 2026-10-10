import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup034
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup035
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup036
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup037
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup038

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow8_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 8 (0, 0)) ≤
      ((161045663394817546404515372521 / 1000000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV8_0Term + (manuscriptNormV8_1Term + (manuscriptNormV8_2Term + (manuscriptNormV8_3Term + (manuscriptNormV8_4Term + (manuscriptNormV8_5Term + (manuscriptNormV8_6Term + (manuscriptNormV8_7Term + (manuscriptNormV8_8Term + (manuscriptNormV8_9Term + (manuscriptNormV8_10Term + (manuscriptNormV8_11Term + (manuscriptNormV8_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV8_0_enclosure.2, manuscriptNormV8_1_enclosure.2, manuscriptNormV8_2_enclosure.2, manuscriptNormV8_3_enclosure.2, manuscriptNormV8_4_enclosure.2, manuscriptNormV8_5_enclosure.2, manuscriptNormV8_6_enclosure.2, manuscriptNormV8_7_enclosure.2, manuscriptNormV8_8_enclosure.2, manuscriptNormV8_9_enclosure.2, manuscriptNormV8_10_enclosure.2, manuscriptNormV8_11_enclosure.2, manuscriptNormV8_12_enclosure.2]

end InternalCatalan

end

end

end OAI
