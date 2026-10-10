import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples13

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_9_9 : GramCompute.ZFast 13 9 9 = (5851440 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_9_11 : GramCompute.ZFast 13 9 11 = (-16839900 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_9_13 : GramCompute.ZFast 13 9 13 = (-36486450 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
