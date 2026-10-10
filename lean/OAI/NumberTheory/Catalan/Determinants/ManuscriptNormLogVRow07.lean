import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup030
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup031
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup032
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup033
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup034

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow7_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 7 (0, 0)) ≤
      ((161045663394817546404515372521 / 1000000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV7_0Term + (manuscriptNormV7_1Term + (manuscriptNormV7_2Term + (manuscriptNormV7_3Term + (manuscriptNormV7_4Term + (manuscriptNormV7_5Term + (manuscriptNormV7_6Term + (manuscriptNormV7_7Term + (manuscriptNormV7_8Term + (manuscriptNormV7_9Term + (manuscriptNormV7_10Term + (manuscriptNormV7_11Term + (manuscriptNormV7_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV7_0_enclosure.2, manuscriptNormV7_1_enclosure.2, manuscriptNormV7_2_enclosure.2, manuscriptNormV7_3_enclosure.2, manuscriptNormV7_4_enclosure.2, manuscriptNormV7_5_enclosure.2, manuscriptNormV7_6_enclosure.2, manuscriptNormV7_7_enclosure.2, manuscriptNormV7_8_enclosure.2, manuscriptNormV7_9_enclosure.2, manuscriptNormV7_10_enclosure.2, manuscriptNormV7_11_enclosure.2, manuscriptNormV7_12_enclosure.2]

end InternalCatalan

end

end

end OAI
