import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples12

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_11_11 : GramCompute.ZFast 12 11 11 = (36018675 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
