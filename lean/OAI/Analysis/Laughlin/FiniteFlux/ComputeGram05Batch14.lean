import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples14

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_14_5_5 : GramCompute.ZFast 14 5 5 = (43545600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

theorem computeGram_14_5_7 : GramCompute.ZFast 14 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

theorem computeGram_14_5_9 : GramCompute.ZFast 14 5 9 = (-21772800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

theorem computeGram_14_5_11 : GramCompute.ZFast 14 5 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

theorem computeGram_14_5_13 : GramCompute.ZFast 14 5 13 = (389188800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_14]
  decide +kernel

end Laughlin.Certificate

end OAI
