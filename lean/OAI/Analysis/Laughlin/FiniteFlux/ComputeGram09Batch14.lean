import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples14

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_14_9_9 : GramCompute.ZFast 14 9 9 = (43545600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

theorem computeGram_14_9_11 : GramCompute.ZFast 14 9 11 = (-44906400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

theorem computeGram_14_9_13 : GramCompute.ZFast 14 9 13 = (-194594400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

end Laughlin.Certificate

end OAI
