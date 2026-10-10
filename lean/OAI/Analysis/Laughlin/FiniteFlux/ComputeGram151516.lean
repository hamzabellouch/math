import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples16

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_15_15 : GramCompute.ZFast 16 15 15 = (2584061605125/2 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
