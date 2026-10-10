import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples19

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_11_11 : GramCompute.ZFast 19 11 11 = (572107536000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_11_13 : GramCompute.ZFast 19 11 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_11_15 : GramCompute.ZFast 19 11 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_11_17 : GramCompute.ZFast 19 11 17 = (-7641722088000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_11_19 : GramCompute.ZFast 19 11 19 = (-29698510842000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
