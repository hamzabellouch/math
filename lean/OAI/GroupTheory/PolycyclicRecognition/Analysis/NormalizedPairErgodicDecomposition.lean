import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairErgodic
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactErgodicDecomposition

namespace OAI

/-! # Unconditional ergodic decomposition on normalized pair spaces -/

noncomputable section

namespace PolycyclicRecognition

open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

theorem normalizedPair_ergodicDecomposition : ErgodicDecompositionInput G (NormalizedPair G Λ) := by
  let : MetricSpace (NormalizedPair G Λ) :=
    TopologicalSpace.metrizableSpaceMetric (NormalizedPair G Λ)
  exact ergodicDecompositionInput_of_compactMetric

end PolycyclicRecognition

end

end OAI
