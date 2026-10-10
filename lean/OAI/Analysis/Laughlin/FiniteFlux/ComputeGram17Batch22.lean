import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples22

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_17_17 : GramCompute.ZFast 22 17 17 = (22841802023040000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_17_19 : GramCompute.ZFast 22 17 19 = (-30292481058840000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_17_21 : GramCompute.ZFast 22 17 21 = (-37420123660920000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
