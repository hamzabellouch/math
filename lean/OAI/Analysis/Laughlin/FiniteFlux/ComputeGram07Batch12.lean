import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples12

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_12_7_7 : GramCompute.ZFast 12 7 7 = (340200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_7_9 : GramCompute.ZFast 12 7 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

theorem computeGram_12_7_11 : GramCompute.ZFast 12 7 11 = (-1871100 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_12]
  decide +kernel

end Laughlin.Certificate

end OAI
