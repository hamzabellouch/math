import Mathlib.MeasureTheory.MeasurableSpace.Invariants
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantDisintegration

namespace OAI

/-! # Conditioning on all invariant measurable sets

The factor retains the original points but equips them with the sigma algebra
of invariant sets. Its conditional kernel is pointwise constant on every orbit
and has the original probability as its barycenter.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set

variable (G X : Type*) [Group G] [mX : MeasurableSpace X] [MulAction G X]

/-- The sigma algebra of measurable sets invariant under the entire action. -/
@[instance_reducible]
def invariantSigma : MeasurableSpace X :=
  ⨅ g : G, MeasurableSpace.invariants (g • ·)

theorem measurableSet_invariantSigma {s : Set X} :
    @MeasurableSet X (invariantSigma G X) s ↔
      @MeasurableSet X mX s ∧ ∀ g : G, (g • ·) ⁻¹' s = s := by
  rw [invariantSigma, MeasurableSpace.measurableSet_iInf]
  simp only [MeasurableSpace.measurableSet_invariants]
  exact ⟨fun h => ⟨(h 1).1, fun g => (h g).2⟩,
    fun h g => ⟨h.1, h.2 g⟩⟩

theorem invariantSigma_le : invariantSigma G X ≤ ‹MeasurableSpace X› :=
  (iInf_le _ (1 : G)).trans (MeasurableSpace.invariants_le _)

/-- The measurable factor, without imposing any quotient topology. -/
structure InvariantFactor (G X : Type*) where
  val : X

instance : MeasurableSpace (InvariantFactor G X) :=
  MeasurableSpace.comap InvariantFactor.val (invariantSigma G X)

/-- Identity on points, with the coarser invariant sigma algebra as codomain. -/
def invariantFactorMap (x : X) : InvariantFactor G X := ⟨x⟩

theorem measurable_invariantFactorMap : Measurable (invariantFactorMap G X) := by
  rw [measurable_iff_comap_le]
  change ((invariantSigma G X).comap InvariantFactor.val).comap (invariantFactorMap G X) ≤ _
  rw [MeasurableSpace.comap_comp]
  change (invariantSigma G X).comap id ≤ _
  rw [MeasurableSpace.comap_id]
  exact invariantSigma_le G X

variable {G X}

/-- Every measurable scalar observable on the factor is exactly orbit invariant. -/
theorem invariantFactor_observable {Z : Type*} [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (f : InvariantFactor G X → Z) (hf : Measurable f)
    (g : G) (x : X) : f (invariantFactorMap G X (g • x)) =
      f (invariantFactorMap G X x) := by
  have hm : @Measurable X (InvariantFactor G X) (invariantSigma G X) _
      (invariantFactorMap G X) := by
    rw [measurable_iff_comap_le]
    change ((invariantSigma G X).comap InvariantFactor.val).comap (invariantFactorMap G X) ≤ _
    rw [MeasurableSpace.comap_comp]
    change (invariantSigma G X).comap id ≤ _
    rw [MeasurableSpace.comap_id]
  have h : @Measurable X Z (MeasurableSpace.invariants (g • ·)) _
      (fun x : X => f (invariantFactorMap G X x)) :=
    (hf.comp hm).mono (iInf_le _ g) le_rfl
  exact congrFun (MeasurableSpace.comp_eq_of_measurable_invariants h) x

variable [StandardBorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Conditional probabilities over the complete invariant sigma algebra. -/
def invariantConditionalKernel : Kernel (InvariantFactor G X) X :=
  factorConditionalKernel μ (invariantFactorMap G X) (measurable_invariantFactorMap G X)

instance invariantConditionalKernel_markov : IsMarkovKernel (invariantConditionalKernel (G := G) μ) := by
  unfold invariantConditionalKernel
  infer_instance

/-- Pull the conditional kernel back to the original space. -/
def invariantConditionalMeasures (x : X) : Measure X :=
  invariantConditionalKernel (G := G) μ (invariantFactorMap G X x)

theorem invariantConditionalMeasures_probability (x : X) :
    IsProbabilityMeasure (invariantConditionalMeasures (G := G) μ x) := by
  unfold invariantConditionalMeasures
  infer_instance

theorem invariantConditionalMeasures_measurable : Measurable (invariantConditionalMeasures (G := G) μ) :=
  (invariantConditionalKernel (G := G) μ).measurable.comp (measurable_invariantFactorMap G X)

theorem invariantConditionalMeasures_smul (g : G) (x : X) :
    invariantConditionalMeasures (G := G) μ (g • x) = invariantConditionalMeasures (G := G) μ x := by
  ext s hs
  exact invariantFactor_observable (fun y => invariantConditionalKernel (G := G) μ y s)
    ((invariantConditionalKernel (G := G) μ).measurable_coe hs) g x

theorem invariantConditionalMeasures_barycenter (s : Set X) (hs : MeasurableSet s) :
    μ s = ∫⁻ x, invariantConditionalMeasures (G := G) μ x s ∂μ :=
  factorConditionalKernel_barycenter μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X) s hs

end PolycyclicRecognition

end

end OAI
