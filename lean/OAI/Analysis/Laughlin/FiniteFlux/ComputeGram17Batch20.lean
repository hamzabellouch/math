import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples20

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_20_17_17 : GramCompute.ZFast 20 17 17 = (1921545754128000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

theorem computeGram_20_17_19 : GramCompute.ZFast 20 17 19 = (-207889575894000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_20]
  decide +kernel

end Laughlin.Certificate

end OAI
