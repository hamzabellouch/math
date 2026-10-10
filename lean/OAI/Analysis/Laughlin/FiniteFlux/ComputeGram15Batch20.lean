import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples20

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_15_15 : GramCompute.ZFast 20 15 15 = (62791356127500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_15_17 : GramCompute.ZFast 20 15 17 = (-182359277100000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_15_19 : GramCompute.ZFast 20 15 19 = (-259861969867500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
