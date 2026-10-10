import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples12

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_3_3 : GramCompute.ZFast 12 3 3 = (2177280 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_5 : GramCompute.ZFast 12 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_7 : GramCompute.ZFast 12 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_9 : GramCompute.ZFast 12 3 9 = (-1088640 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_3_11 : GramCompute.ZFast 12 3 11 = (7484400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
