import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples14

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_14_11_11 : GramCompute.ZFast 14 11 11 = (85135050 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

theorem computeGram_14_11_13 : GramCompute.ZFast 14 11 13 = (-243243000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

end Laughlin.Certificate

end OAI
