import OAI.NumberTheory.DukePrimeDegree.Geometry.CountableWeakTests
import Mathlib.Topology.Sequences

namespace OAI

/-!
# A probability kernel is measurable for the weak topology

A countable family of finite-basis-union evaluations defines a stronger
second-countable topology on probabilities. Kernel evaluations are measurable
for that topology, and the countable Portmanteau criterion makes the map
to the usual weak topology continuous. No global measurable-space
instance on probabilities is changed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology ENNReal

namespace DukePrimeDegree

variable (Y : Type*) [TopologicalSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- A separate wrapper retains both probability topologies without
overriding the existing weak topology. -/
structure BasisProbability where
  toProbability : ProbabilityMeasure Y

def basisProbabilityTests (p : BasisProbability Y) :
    Finset (countableBasis Y) → ℝ≥0∞ :=
  fun F => (p.toProbability : Measure Y) (finiteBasisUnion F)

instance : TopologicalSpace (BasisProbability Y) :=
  TopologicalSpace.induced (basisProbabilityTests Y) inferInstance

omit [OpensMeasurableSpace Y] in
lemma basisProbabilityTests_isInducing :
    Topology.IsInducing (basisProbabilityTests Y) := ⟨rfl⟩

instance : SecondCountableTopology (BasisProbability Y) :=
  (basisProbabilityTests_isInducing Y).secondCountableTopology

instance : MeasurableSpace (BasisProbability Y) := borel (BasisProbability Y)

instance : BorelSpace (BasisProbability Y) := ⟨rfl⟩

theorem continuous_basisProbability_toProbability :
    Continuous (BasisProbability.toProbability (Y := Y)) := by
  apply continuous_iff_seqContinuous.mpr
  intro u p hu
  apply tendsto_probability_of_finiteBasisUnion
  intro F
  exact ((continuous_apply F).comp (basisProbabilityTests_isInducing Y).continuous).continuousAt.tendsto.comp hu

variable {Y}

theorem measurable_kernel_basisProbability
    {Z : Type*} [MeasurableSpace Z] (κ : Kernel Z Y) [IsMarkovKernel κ] :
    Measurable (fun z =>
      (⟨⟨κ z, inferInstance⟩⟩ : BasisProbability Y)) := by
  have hm : Measurable (fun z => basisProbabilityTests Y
      (⟨⟨κ z, inferInstance⟩⟩ : BasisProbability Y)) := by
    apply measurable_pi_iff.mpr
    intro F
    exact measurable_kernel_finiteBasisUnion κ F
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (fun z =>
      (⟨⟨κ z, inferInstance⟩⟩ : BasisProbability Y))
    (@borel (BasisProbability Y) (TopologicalSpace.induced (basisProbabilityTests Y) _)) ≤ _
  rw [borel_comap, MeasurableSpace.comap_comp,
    ← BorelSpace.measurable_eq (α := Finset (countableBasis Y) → ℝ≥0∞)]
  exact hm.comap_le

/-- The codomain carries the Borel sigma algebra of weak convergence. -/
theorem measurable_kernel_probability_weak
    {Z : Type*} [mZ : MeasurableSpace Z] (κ : Kernel Z Y) [IsMarkovKernel κ] :
    @Measurable Z (ProbabilityMeasure Y) mZ (borel (ProbabilityMeasure Y))
      (fun z => ⟨κ z, inferInstance⟩) := by
  have hcont := (continuous_basisProbability_toProbability Y).borel_measurable
  exact hcont.comp (measurable_kernel_basisProbability κ)

end DukePrimeDegree

end

end OAI
