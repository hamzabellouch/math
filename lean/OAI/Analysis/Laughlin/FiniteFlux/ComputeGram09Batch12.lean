import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples12

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_9_9 : GramCompute.ZFast 12 9 9 = (544320 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_9_11 : GramCompute.ZFast 12 9 11 = (-3742200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
