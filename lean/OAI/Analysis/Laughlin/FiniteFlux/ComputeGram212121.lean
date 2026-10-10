import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples21

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_21_21_21 : GramCompute.ZFast 21 21 21 = (102179740482167473125/2 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

end Laughlin.Certificate

end OAI
