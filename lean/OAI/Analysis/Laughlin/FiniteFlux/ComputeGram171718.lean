import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples18

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_17_17 : GramCompute.ZFast 18 17 17 = (354298024080000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
