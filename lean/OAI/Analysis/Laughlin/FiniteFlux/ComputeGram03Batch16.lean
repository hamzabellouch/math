import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples16

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_3_3 : GramCompute.ZFast 16 3 3 = (37362124800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_5 : GramCompute.ZFast 16 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_7 : GramCompute.ZFast 16 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_9 : GramCompute.ZFast 16 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_11 : GramCompute.ZFast 16 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_13 : GramCompute.ZFast 16 3 13 = (-7005398400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_3_15 : GramCompute.ZFast 16 3 15 = (102162060000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
