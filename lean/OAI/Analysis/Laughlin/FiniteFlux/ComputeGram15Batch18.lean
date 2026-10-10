import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples18

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_15_15 : GramCompute.ZFast 18 15 15 = (6169949911125 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_15_17 : GramCompute.ZFast 18 15 17 = (-1823592771000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
