import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples16

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_9_9 : GramCompute.ZFast 16 9 9 = (457228800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_9_11 : GramCompute.ZFast 16 9 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_9_13 : GramCompute.ZFast 16 9 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_9_15 : GramCompute.ZFast 16 9 15 = (-10216206000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
