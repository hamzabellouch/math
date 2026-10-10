import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples17

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_17_17_17 : GramCompute.ZFast 17 17 17 = (355589735626125 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

end Laughlin.Certificate

end OAI
