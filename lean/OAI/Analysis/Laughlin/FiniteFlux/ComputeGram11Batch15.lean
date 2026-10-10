import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples15

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_15_11_11 : GramCompute.ZFast 15 11 11 = (340540200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_11_13 : GramCompute.ZFast 15 11 13 = (-1605403800 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_11_15 : GramCompute.ZFast 15 11 15 = (-2554051500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

end Laughlin.Certificate

end OAI
