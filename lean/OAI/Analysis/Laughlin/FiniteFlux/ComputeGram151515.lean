import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples15

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_15_15_15 : GramCompute.ZFast 15 15 15 = (1306397342250 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

end Laughlin.Certificate

end OAI
