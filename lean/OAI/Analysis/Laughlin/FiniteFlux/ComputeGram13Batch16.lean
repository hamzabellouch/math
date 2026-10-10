import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples16

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_13_13 : GramCompute.ZFast 16 13 13 = (22183761600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_13_15 : GramCompute.ZFast 16 13 15 = (-19155386250 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
