import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples17

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_17_13_13 : GramCompute.ZFast 17 13 13 = (55532376900 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_13_15 : GramCompute.ZFast 17 13 15 = (-166013347500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_13_17 : GramCompute.ZFast 17 13 17 = (-217094377500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

end Laughlin.Certificate

end OAI
