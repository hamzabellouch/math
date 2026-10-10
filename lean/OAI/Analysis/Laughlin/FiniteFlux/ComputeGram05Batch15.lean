import OAI.Analysis.Laughlin.FiniteFlux.ComputeQuadruples15

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_15_5_5 : GramCompute.ZFast 15 5 5 = (435456000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_5_7 : GramCompute.ZFast 15 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_5_9 : GramCompute.ZFast 15 5 9 = (-40824000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_5_11 : GramCompute.ZFast 15 5 11 = (-299376000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_5_13 : GramCompute.ZFast 15 5 13 = (1459458000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

theorem computeGram_15_5_15 : GramCompute.ZFast 15 5 15 = (10216206000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_15]
  decide +kernel

end Laughlin.Certificate

end OAI
