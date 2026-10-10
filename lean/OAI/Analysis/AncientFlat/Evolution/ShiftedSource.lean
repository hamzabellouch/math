import OAI.Analysis.AncientFlat.Evolution.MovingSource

namespace OAI
open Set
open scoped ZeroAtInfty BoundedContinuousFunction
open ParametrixDilation ParametrixEvolution FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma shiftedSource_apply (f : ℝ →ᵇ C₀(V,ℂ)) (s t : ℝ) : shiftedSource f s t = dil s (f (s+t)) := by rfl

end OAI
