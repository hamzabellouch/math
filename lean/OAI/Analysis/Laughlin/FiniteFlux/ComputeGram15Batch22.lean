import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples22

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_15_15 : GramCompute.ZFast 22 15 15 = (5440206316545000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_15_17 : GramCompute.ZFast 22 15 17 = (-8534414168280000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_15_19 : GramCompute.ZFast 22 15 19 = (-23387577288075000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_15_21 : GramCompute.ZFast 22 15 21 = (-43656810937740000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
