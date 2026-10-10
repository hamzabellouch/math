import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples21

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_21_15_15 : GramCompute.ZFast 21 15 15 = (481336545690000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

theorem computeGram_21_15_17 : GramCompute.ZFast 21 15 17 = (-1422402361380000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

theorem computeGram_21_15_19 : GramCompute.ZFast 21 15 19 = (-2672865975780000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

theorem computeGram_21_15_21 : GramCompute.ZFast 21 15 21 = (-3897929548012500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

end Laughlin.Certificate

end OAI
