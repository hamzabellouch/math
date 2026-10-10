import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples14

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_14_7_7 : GramCompute.ZFast 14 7 7 = (11113200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

theorem computeGram_14_7_9 : GramCompute.ZFast 14 7 9 = (-19051200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

theorem computeGram_14_7_11 : GramCompute.ZFast 14 7 11 = (26195400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

theorem computeGram_14_7_13 : GramCompute.ZFast 14 7 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

end Laughlin.Certificate

end OAI
