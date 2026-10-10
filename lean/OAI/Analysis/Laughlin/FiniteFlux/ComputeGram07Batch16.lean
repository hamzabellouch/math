import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples16

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_16_7_7 : GramCompute.ZFast 16 7 7 = (1828915200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_7_9 : GramCompute.ZFast 16 7 9 = (-685843200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_7_11 : GramCompute.ZFast 16 7 11 = (-1571724000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_7_13 : GramCompute.ZFast 16 7 13 = (4086482400 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

theorem computeGram_16_7_15 : GramCompute.ZFast 16 7 15 = (15324309000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_16]
  decide +kernel

end Laughlin.Certificate

end OAI
