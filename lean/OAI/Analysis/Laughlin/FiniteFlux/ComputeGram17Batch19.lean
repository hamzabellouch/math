import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples19

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_19_17_17 : GramCompute.ZFast 19 17 17 = (693290894546250 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

theorem computeGram_19_17_19 : GramCompute.ZFast 19 17 19 = (-14849255421000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_19]
  decide +kernel

end Laughlin.Certificate

end OAI
