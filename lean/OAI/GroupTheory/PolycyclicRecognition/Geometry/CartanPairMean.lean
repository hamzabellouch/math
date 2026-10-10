import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairMeanControl
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHomKernel

namespace OAI

/-! # The actual averaged slope kills the Cartan root factor

This applies the metric estimate for normalized pairs and the root-flow
argument to the very homomorphism used by the stationary L² theorem.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open MeasureTheory LieAlgebra
open scoped Manifold NNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Λ K : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
  [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T M

/-- No geometric factorization is assumed for the averaged slope. Its
vanishing on the entire actual root factor follows from distortion. -/
theorem normalizedPairMeanSlope_kills_root_factor
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (π : G →* Multiplicative W)
    (hπ : LipschitzWith K (fun g => (π g).toAdd)) (n : F.N.carrier) :
    normalizedPairMeanSlope μ π hπ.continuous (F.inclusionN n) = 1 := by
  apply M.hom_eq_one_on_root_factor T hExp realize
    (normalizedPairMeanSlope μ π hπ.continuous)
    (continuous_normalizedPairMeanSlope μ π hπ.continuous)
    (mul_nonneg K.coe_nonneg Λ.coe_nonneg)
    (norm_normalizedPairMeanSlope_le μ π hπ) F haarN dynkinN n

end PolycyclicRecognition.CartanWordModel

end

end OAI
