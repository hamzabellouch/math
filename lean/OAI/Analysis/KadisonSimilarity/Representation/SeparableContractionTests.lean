import OAI.Analysis.KadisonSimilarity.Representation.CountableFiberTests
import Mathlib.Topology.Bases

namespace OAI

/-! # Countable weak-operator contraction tests

On a separable Hilbert space, the weak-operator unit ball embeds in a countable
product of copies of `ℂ`, by its coefficients on a dense sequence of vectors.
Compactness makes this an embedding. Thus each von Neumann algebra has a
countable weakly dense family of contractions.
-/

noncomputable section

namespace KadisonSimilarity

open ContinuousLinearMapWOT
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- The operator unit ball, with the topology induced by the weak-operator
topology. -/
abbrev WeakOperatorUnitBall (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] :=
  {T : H →WOT[ℂ] H // ‖toCLM T‖ ≤ 1}

/-- Countably many matrix coefficients determine the topology on the weak
operator unit ball of a separable Hilbert space. -/
theorem secondCountable_weakOperatorUnitBall :
    SecondCountableTopology (WeakOperatorUnitBall H) := by
  let d : ℕ → H := TopologicalSpace.denseSeq H
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq H
  let f : WeakOperatorUnitBall H → ℕ → ℕ → ℂ :=
    fun T i j => inner ℂ (d i) ((T : H →WOT[ℂ] H) (d j))
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val (d j) (d i)
  have hinj : Function.Injective f := by
    intro S T h
    apply Subtype.ext
    apply ContinuousLinearMapWOT.ext_inner
    intro x y
    apply hd.induction_on₂ (p := fun x y =>
      inner ℂ y ((S : H →WOT[ℂ] H) x) = inner ℂ y ((T : H →WOT[ℂ] H) x))
      (isClosed_eq (by fun_prop) (by fun_prop)) _ x y
    intro i j
    exact congrFun (congrFun h j) i
  let : CompactSpace (WeakOperatorUnitBall H) :=
    isCompact_iff_compactSpace.mp (isCompact_weakOperator_ball (H := H) 1 zero_le_one)
  exact (hf.isClosedEmbedding hinj).isEmbedding.secondCountableTopology

/-- A concrete von Neumann algebra on a separable Hilbert space has a
countable weak-operator dense family in its closed unit ball. -/
theorem exists_separable_contraction_tests (P : VonNeumannAlgebra H) :
    ∃ test : ℕ → P.toStarSubalgebra,
      (∀ n, ‖test n‖ ≤ 1) ∧
      ∀ T : H →L[ℂ] H, T ∈ P → ‖T‖ ≤ 1 →
        ofCLM T ∈ closure (Set.range fun n => ofCLM (test n : H →L[ℂ] H)) := by
  let : SecondCountableTopology (WeakOperatorUnitBall H) :=
    secondCountable_weakOperatorUnitBall
  let B := {T : WeakOperatorUnitBall H // toCLM T.val ∈ P}
  let : SecondCountableTopology B :=
    (show Topology.IsEmbedding (Subtype.val : B → WeakOperatorUnitBall H) from
      Topology.IsEmbedding.subtypeVal).secondCountableTopology
  let : TopologicalSpace.SeparableSpace B := inferInstance
  let : Nonempty B := ⟨⟨⟨ofCLM 0, by simp⟩, P.zero_mem⟩⟩
  let d : ℕ → B := TopologicalSpace.denseSeq B
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq B
  let test : ℕ → P.toStarSubalgebra :=
    fun n => ⟨toCLM (d n).val.val, (d n).property⟩
  refine ⟨test, fun n => (d n).val.property, ?_⟩
  intro T hT hn
  let t : B := ⟨⟨ofCLM T, hn⟩, hT⟩
  let inclusion : B → H →WOT[ℂ] H := fun x => x.val.val
  have hc : Continuous inclusion := continuous_subtype_val.comp continuous_subtype_val
  change inclusion t ∈ _
  exact map_mem_closure (f := inclusion) hc (hd t) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, rfl⟩)

/-- It suffices to verify the scalar commutator bound on some countable family
of contractions, constructed from separability. -/
theorem exists_countable_scalar_commutator_tests (P : VonNeumannAlgebra H) :
    ∃ test : ℕ → P.toStarSubalgebra,
      (∀ n, ‖test n‖ ≤ 1) ∧
      ∀ (Y : H →L[ℂ] H) (c : ℝ), 0 ≤ c →
        (∀ n, ‖commutator Y (test n)‖ ≤ c) → scalarCommutatorNorm P Y ≤ c := by
  obtain ⟨test, hnorm, hdense⟩ := exists_separable_contraction_tests P
  refine ⟨test, hnorm, ?_⟩
  intro Y c hc hbound
  exact scalarCommutatorNorm_le_of_weak_dense_tests P Y
    (fun n => (test n : H →L[ℂ] H)) hdense hc hbound

end KadisonSimilarity

end

end OAI
