import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples23

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_17_17 : GramCompute.ZFast 23 17 17 = (111009907368360000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_17_19 : GramCompute.ZFast 23 17 19 = (-302924810588400000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_17_21 : GramCompute.ZFast 23 17 21 = (-463853616213487500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_17_23 : GramCompute.ZFast 23 17 23 = (-591705705388297500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
