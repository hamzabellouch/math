import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples18

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_11_11 : GramCompute.ZFast 18 11 11 = (149313780000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_11_13 : GramCompute.ZFast 18 11 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_11_15 : GramCompute.ZFast 18 11 15 = (-421418497500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_11_17 : GramCompute.ZFast 18 11 17 = (-1736755020000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
