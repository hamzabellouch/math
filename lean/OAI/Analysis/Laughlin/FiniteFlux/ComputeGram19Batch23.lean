import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples23

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_19_19 : GramCompute.ZFast 23 19 19 = (2530981340232345000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_19_21 : GramCompute.ZFast 23 19 21 = (-414739703908530000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_19_23 : GramCompute.ZFast 23 19 23 = (-394470470258865000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
