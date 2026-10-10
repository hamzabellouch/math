import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples22

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_21_21 : GramCompute.ZFast 22 21 21 = (51071452523969377500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
