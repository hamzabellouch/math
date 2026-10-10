import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples13

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_7_7 : GramCompute.ZFast 13 7 7 = (453600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_7_9 : GramCompute.ZFast 13 7 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_7_11 : GramCompute.ZFast 13 7 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_7_13 : GramCompute.ZFast 13 7 13 = (-24324300 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
