import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples18

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_9_9 : GramCompute.ZFast 18 9 9 = (98761420800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_9_11 : GramCompute.ZFast 18 9 11 = (-113164128000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_9_13 : GramCompute.ZFast 18 9 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_9_15 : GramCompute.ZFast 18 9 15 = (367783416000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_9_17 : GramCompute.ZFast 18 9 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
