import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples20

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_19_19 : GramCompute.ZFast 20 19 19 = (121494751697694375 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
