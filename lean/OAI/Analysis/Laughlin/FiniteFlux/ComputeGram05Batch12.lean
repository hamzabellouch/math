import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples12

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_5_5 : GramCompute.ZFast 12 5 5 = (604800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_5_7 : GramCompute.ZFast 12 5 7 = (-453600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_5_9 : GramCompute.ZFast 12 5 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_5_11 : GramCompute.ZFast 12 5 11 = (2494800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
