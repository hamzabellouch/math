import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup039
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup040
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup041
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup042
import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup043

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem manuscriptNormVRow9_upper :
    manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 9 (0, 0)) ≤
      ((-13331960711348427692491383349 / 250000000000000000000000000000) : ℝ) := by
  change (manuscriptNormV9_0Term + (manuscriptNormV9_1Term + (manuscriptNormV9_2Term + (manuscriptNormV9_3Term + (manuscriptNormV9_4Term + (manuscriptNormV9_5Term + (manuscriptNormV9_6Term + (manuscriptNormV9_7Term + (manuscriptNormV9_8Term + (manuscriptNormV9_9Term + (manuscriptNormV9_10Term + (manuscriptNormV9_11Term + (manuscriptNormV9_12Term + (0 : ℝ)))))))))))))) ≤ _
  linarith only [manuscriptNormV9_0_enclosure.2, manuscriptNormV9_1_enclosure.2, manuscriptNormV9_2_enclosure.2, manuscriptNormV9_3_enclosure.2, manuscriptNormV9_4_enclosure.2, manuscriptNormV9_5_enclosure.2, manuscriptNormV9_6_enclosure.2, manuscriptNormV9_7_enclosure.2, manuscriptNormV9_8_enclosure.2, manuscriptNormV9_9_enclosure.2, manuscriptNormV9_10_enclosure.2, manuscriptNormV9_11_enclosure.2, manuscriptNormV9_12_enclosure.2]

end InternalCatalan

end

end

end OAI
