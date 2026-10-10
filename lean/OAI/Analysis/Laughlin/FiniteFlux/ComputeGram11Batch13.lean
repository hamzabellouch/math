import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples13

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_13_11_11 : GramCompute.ZFast 13 11 11 = (52390800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

theorem computeGram_13_11_13 : GramCompute.ZFast 13 11 13 = (-30405375 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_13]
  decide +kernel

end Laughlin.Certificate

end OAI
