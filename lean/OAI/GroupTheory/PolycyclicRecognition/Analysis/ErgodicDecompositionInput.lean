import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationaryProbability
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! # Ergodic decomposition of invariant probabilities

Greschonig--Schmidt, *Ergodic decomposition of quasi-invariant probability
measures*, Colloquium Mathematicum 84/85 (2000), 495--514, Theorem 5.2(1),
specialized to the zero Radon--Nikodym cocycle. Components are invariant
ergodic probabilities and their barycenter is the original measure. The
formalization records setwise measurability, the barycenter identity, and
invariance of the component map.

Source: https://www.mat.univie.ac.at/~kschmidt/Publications/decomposition.pdf
-/

namespace PolycyclicRecognition

open MeasureTheory

/-- The invariant specialization of Greschonig--Schmidt Theorem 5.2.
All topological and standard-Borel hypotheses are retained in the binder. -/
def ErgodicDecompositionInput (G X : Type*)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [MulAction G X] [ContinuousSMul G X] : Prop :=
  ∀ μ : Measure X, IsProbabilityMeasure μ → SMulInvariantMeasure G X μ →
    ∃ κ : X → Measure X,
      (∀ x, IsProbabilityMeasure (κ x) ∧ ErgodicSMul G X (κ x)) ∧
      (∀ (g : G) (x : X), κ (g • x) = κ x) ∧
      ∀ s : Set X, MeasurableSet s →
        Measurable (fun x => κ x s) ∧ μ s = ∫⁻ x, κ x s ∂μ

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
  [MulAction G X] [ContinuousSMul G X]

/-- Only the existence of one component is needed for the first stationary
comparison; the stronger setwise statement is retained for the later coupling. -/
theorem exists_ergodic_probability_of_decomposition
    (hdec : ErgodicDecompositionInput G X)
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ] :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ErgodicSMul G X ν := by
  obtain ⟨κ, hκ, _⟩ := hdec μ inferInstance inferInstance
  have : Nonempty X := MeasureTheory.nonempty_of_isProbabilityMeasure μ
  obtain ⟨x⟩ := this
  exact ⟨κ x, hκ x⟩

/-- An actual invariant mean followed by the published decomposition supplies
an ergodic probability on a nonempty compact action space. -/
theorem exists_ergodic_probability_of_mean [CompactSpace X] [T2Space X] [Nonempty X]
    (M : ThompsonNonamenability.InvariantMean G)
    (hdec : ErgodicDecompositionInput G X) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ErgodicSMul G X ν := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact exists_ergodic_probability_of_decomposition hdec (orbitProbability M x)

end PolycyclicRecognition

end OAI
