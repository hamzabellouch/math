import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples17

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_17_11_11 : GramCompute.ZFast 17 11 11 = (28740096000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_11_13 : GramCompute.ZFast 17 11 13 = (-24081057000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_11_15 : GramCompute.ZFast 17 11 15 = (-112378266000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

theorem computeGram_17_11_17 : GramCompute.ZFast 17 11 17 = (-260513253000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_17]
  decide +kernel

end Laughlin.Certificate

end OAI
