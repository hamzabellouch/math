import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples21

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_21_13_13 : GramCompute.ZFast 21 13 13 = (198480450168000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

theorem computeGram_21_13_15 : GramCompute.ZFast 21 13 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

theorem computeGram_21_13_17 : GramCompute.ZFast 21 13 17 = (-447040742148000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

theorem computeGram_21_13_19 : GramCompute.ZFast 21 13 19 = (-1930403204730000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

theorem computeGram_21_13_21 : GramCompute.ZFast 21 13 21 = (-4677515457615000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

end Laughlin.Certificate

end OAI
