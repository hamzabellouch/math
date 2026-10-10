import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

/-!
# The entropy functional in the published dynamical inputs

A finite measurable partition is represented by its finite-valued label
map. Its length-`N` names encode the join of its first `N` inverse images
under the transformation. The liminf definition agrees with the usual
limit for invariant probabilities by subadditivity; proving that agreement
and the published entropy theorems is still part of the outstanding work.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DukePrimeDegree

/-- A finite measurable partition, allowing empty atoms. -/
structure MeasurablePartition (X : Type*) [MeasurableSpace X] (k : ℕ) where
  label : X → Fin (k + 1)
  measurable_label : Measurable label

/-- The atoms of the joined partition through time `N-1`. -/
def nameAtom {X : Type*} [MeasurableSpace X] {k : ℕ}
    (P : MeasurablePartition X k) (T : X → X) (N : ℕ)
    (word : Fin N → Fin (k + 1)) : Set X :=
  {x | ∀ j : Fin N, P.label (T^[j.val] x) = word j}

/-- Shannon entropy of the finite joined partition, with natural logs. -/
noncomputable def blockEntropy {X : Type*} [MeasurableSpace X] {k : ℕ}
    (P : MeasurablePartition X k) (T : X → X) (μ : Measure X) (N : ℕ) : ℝ :=
  ∑ word : Fin N → Fin (k + 1),
    Real.negMulLog (μ (nameAtom P T N word)).toReal

/-- Entropy rate of one partition. The indexing `N+1` avoids division by zero. -/
noncomputable def partitionEntropyRate {X : Type*} [MeasurableSpace X] {k : ℕ}
    (P : MeasurablePartition X k) (T : X → X) (μ : Measure X) : ℝ≥0∞ :=
  liminf (fun N : ℕ => ENNReal.ofReal (blockEntropy P T μ (N + 1) / (N + 1))) atTop

/-- Kolmogorov--Sinai entropy, as the supremum over finite measurable partitions. -/
noncomputable def metricEntropy {X : Type*} [MeasurableSpace X]
    (T : X → X) (μ : Measure X) : ℝ≥0∞ :=
  ⨆ k : ℕ, ⨆ P : MeasurablePartition X k, partitionEntropyRate P T μ

end DukePrimeDegree

end OAI
