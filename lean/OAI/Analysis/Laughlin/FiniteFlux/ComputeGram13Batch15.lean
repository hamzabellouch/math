import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples15

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_15_13_13 : GramCompute.ZFast 15 13 13 = (10477692225 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_13_15 : GramCompute.ZFast 15 13 15 = (-1915538625 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

end Laughlin.Certificate

end OAI
