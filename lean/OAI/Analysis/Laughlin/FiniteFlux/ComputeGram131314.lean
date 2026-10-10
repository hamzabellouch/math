import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples14

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_14_13_13 : GramCompute.ZFast 14 13 13 = (6008102100 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

end Laughlin.Certificate

end OAI
