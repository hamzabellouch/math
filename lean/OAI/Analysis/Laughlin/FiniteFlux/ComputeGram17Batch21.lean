import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples21

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_21_17_17 : GramCompute.ZFast 21 17 17 = (6322135623804000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

theorem computeGram_21_17_19 : GramCompute.ZFast 21 17 19 = (-2650592092648500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

theorem computeGram_21_17_21 : GramCompute.ZFast 21 17 21 = (-2728550683608750 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_21]
  decide +kernel

end Laughlin.Certificate

end OAI
