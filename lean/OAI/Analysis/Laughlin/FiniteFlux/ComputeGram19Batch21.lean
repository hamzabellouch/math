import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples21

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_21_19_19 : GramCompute.ZFast 21 19 19 = (241033113993672000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

theorem computeGram_21_19_21 : GramCompute.ZFast 21 19 21 = (-1754068296605625 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

end Laughlin.Certificate

end OAI
