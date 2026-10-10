import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples19

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_13_13 : GramCompute.ZFast 19 13 13 = (3544293753000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_13_15 : GramCompute.ZFast 19 13 15 = (-6574128561000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_13_17 : GramCompute.ZFast 19 13 17 = (-16933361445000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_13_19 : GramCompute.ZFast 19 13 19 = (-29698510842000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
