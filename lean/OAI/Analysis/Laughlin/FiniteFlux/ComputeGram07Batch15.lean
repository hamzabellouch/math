import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples15

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_15_7_7 : GramCompute.ZFast 15 7 7 = (177811200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_7_9 : GramCompute.ZFast 15 7 9 = (-171460800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_7_11 : GramCompute.ZFast 15 7 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_7_13 : GramCompute.ZFast 15 7 13 = (681080400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_7_15 : GramCompute.ZFast 15 7 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

end Laughlin.Certificate

end OAI
