import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairAction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ErgodicDecompositionInput
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.Urysohn

namespace OAI

/-! # Ergodic probabilities on compact normalized sections

Second countability of the model group gives a Polish topology on the
compact normalized section. Ergodic decomposition therefore applies to
its invariant probabilities.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] {Λ : ℝ≥0}

instance normalizedPair_polishSpace : PolishSpace (NormalizedPair G Λ) := by
  let : MetricSpace (NormalizedPair G Λ) :=
    TopologicalSpace.metrizableSpaceMetric (NormalizedPair G Λ)
  infer_instance

variable [IsTopologicalGroup G] [IsIsometricSMul G G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- All the measurable-space hypotheses of the published decomposition
theorem are discharged on the actual normalized pair space. -/
theorem exists_normalizedPair_ergodic_probability
    [Nonempty (NormalizedPair G Λ)]
    (M : ThompsonNonamenability.InvariantMean G)
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ)) :
    ∃ μ : Measure (NormalizedPair G Λ),
      IsProbabilityMeasure μ ∧ ErgodicSMul G (NormalizedPair G Λ) μ :=
  exists_ergodic_probability_of_mean M hdec

end PolycyclicRecognition

end

end OAI
