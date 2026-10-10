import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples22

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_19_19 : GramCompute.ZFast 22 19 19 = (698765124659852250 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_19_21 : GramCompute.ZFast 22 19 21 = (-28065092745690000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
