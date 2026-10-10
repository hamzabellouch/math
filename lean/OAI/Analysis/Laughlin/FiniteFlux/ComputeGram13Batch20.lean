import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples20

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_13_13 : GramCompute.ZFast 20 13 13 = (31384184832000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_13_15 : GramCompute.ZFast 20 13 15 = (-21913761870000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_13_17 : GramCompute.ZFast 20 13 17 = (-108373513248000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_13_19 : GramCompute.ZFast 20 13 19 = (-267286597578000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
