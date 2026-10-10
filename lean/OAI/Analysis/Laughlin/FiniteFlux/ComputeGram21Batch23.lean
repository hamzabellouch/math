import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples23

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_23_21_21 : GramCompute.ZFast 23 21 21 = (101850365435360416875 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

theorem computeGram_23_21_23 : GramCompute.ZFast 23 21 23 = (-246544043911790625 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_23]
  decide +kernel

end Laughlin.Certificate

end OAI
