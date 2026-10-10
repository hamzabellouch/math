import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples23

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_23_23 : GramCompute.ZFast 23 23 23 = (25851868812458629565625 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
