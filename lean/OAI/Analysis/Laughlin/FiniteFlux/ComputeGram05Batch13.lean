import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples13

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_5_5 : GramCompute.ZFast 13 5 5 = (4838400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_5_7 : GramCompute.ZFast 13 5 7 = (-907200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_5_9 : GramCompute.ZFast 13 5 9 = (-4082400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_5_11 : GramCompute.ZFast 13 5 11 = (12474000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_5_13 : GramCompute.ZFast 13 5 13 = (48648600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
