import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples19

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_15_15 : GramCompute.ZFast 19 15 15 = (17439063642000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_15_17 : GramCompute.ZFast 19 15 17 = (-19538493975000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_15_19 : GramCompute.ZFast 19 15 19 = (-22273883131500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
