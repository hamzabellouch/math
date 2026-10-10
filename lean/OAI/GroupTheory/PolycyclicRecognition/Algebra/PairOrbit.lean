import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairErgodic
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ErgodicMap

namespace OAI

/-!+# Compact invariant orbit closures of individual pairs

The stationary construction can be performed inside the orbit closure of
the given quasi-isometry pair, rather than on an unrelated part of the full
pair space. The orbit closure carries the restricted continuous action.
-/

noncomputable section

open Set MeasureTheory
open scoped NNReal Pointwise

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

/-- The actual orbit closure of a normalized quasi-isometry pair. -/
def PairOrbit (p : NormalizedPair G Λ) := closure (MulAction.orbit G p)

instance (p : NormalizedPair G Λ) : CompactSpace (PairOrbit p) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

instance (p : NormalizedPair G Λ) : Nonempty (PairOrbit p) :=
  ⟨⟨p, subset_closure (MulAction.mem_orbit_self p)⟩⟩

instance pairOrbitAction (p : NormalizedPair G Λ) : MulAction G (PairOrbit p) where
  smul g q := ⟨g • q.val, smul_closure_orbit_subset g p
    (Set.smul_mem_smul_set q.property)⟩
  one_smul q := Subtype.ext (one_smul G q.val)
  mul_smul g h q := Subtype.ext (mul_smul g h q.val)

@[simp] theorem pairOrbit_smul_val (p : NormalizedPair G Λ) (g : G) (q : PairOrbit p) :
    (g • q).val = g • q.val := rfl

instance pairOrbitContinuousAction (p : NormalizedPair G Λ) :
    ContinuousSMul G (PairOrbit p) where
  continuous_smul :=
    (continuous_fst.smul continuous_snd.subtype_val).subtype_mk _

instance pairOrbit_polishSpace [SecondCountableTopology G] (p : NormalizedPair G Λ) :
    PolishSpace (PairOrbit p) := isClosed_closure.polishSpace

/-- A stationary measure supported on the orbit closure of the chosen pair.
Both amenability and the decomposition input are used at that precise space. -/
theorem exists_pairOrbit_ergodic_probability [SecondCountableTopology G]
    (p : NormalizedPair G Λ) [MeasurableSpace (PairOrbit p)] [BorelSpace (PairOrbit p)]
    (M : ThompsonNonamenability.InvariantMean G)
    (hdec : ErgodicDecompositionInput G (PairOrbit p)) :
    ∃ μ : Measure (PairOrbit p),
      IsProbabilityMeasure μ ∧ ErgodicSMul G (PairOrbit p) μ :=
  exists_ergodic_probability_of_mean M hdec

/-- Push the orbit measure to the full pair space. The measure remains
ergodic, so it admits the height cocycle. -/
theorem pairOrbit_pushforward_ergodic (p : NormalizedPair G Λ)
    [MeasurableSpace (PairOrbit p)] [BorelSpace (PairOrbit p)]
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    (μ : Measure (PairOrbit p)) [ErgodicSMul G (PairOrbit p) μ] :
    ErgodicSMul G (NormalizedPair G Λ) (μ.map Subtype.val) :=
  ergodicSMul_map μ Subtype.val continuous_subtype_val.measurable
    (fun _ _ => rfl)

end PolycyclicRecognition

end

end OAI
