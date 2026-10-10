import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples18

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_18_13_13 : GramCompute.ZFast 18 13 13 = (329837508000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_13_15 : GramCompute.ZFast 18 13 15 = (-1195296102000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

theorem computeGram_18_13_17 : GramCompute.ZFast 18 13 17 = (-2084106024000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_18]
  decide +kernel

end Laughlin.Certificate

end OAI
