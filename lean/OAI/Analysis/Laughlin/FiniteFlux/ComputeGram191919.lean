import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples19

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_19_19 : GramCompute.ZFast 19 19 19 = (121635819624193875 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
