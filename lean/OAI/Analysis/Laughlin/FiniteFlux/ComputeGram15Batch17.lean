import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples17

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_17_15_15 : GramCompute.ZFast 17 15 15 = (2442950259750 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_15_17 : GramCompute.ZFast 17 15 17 = (-151966064250 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

end Laughlin.Certificate

end OAI
