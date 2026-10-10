import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples13

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_13_13 : GramCompute.ZFast 13 13 13 = (12411474075/2 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
