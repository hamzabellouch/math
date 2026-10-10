import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantFactor
import OAI.GroupTheory.PolycyclicRecognition.Analysis.DenseInvariantMeasure

namespace OAI

/-! # Invariance of the conditional component measures

Only countably many identities are intersected. Continuity of the action
extends invariance from the dense sequence to the full acting group.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory TopologicalSpace

variable {G X Y : Type*} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [MulAction G X] [ContinuousSMul G X]
  (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]
  (f : X → Y) (hf : Measurable f)

/-- The invariant factor may have a sigma algebra that is not countably generated. -/
theorem factorConditionalKernel_invariant_ae_dense
    (hfi : ∀ (g : G) (s : Set Y), MeasurableSet s →
      ∀ x, f (g • x) ∈ s ↔ f x ∈ s) :
    ∀ᵐ y ∂μ.map f, SMulInvariantMeasure G X (factorConditionalKernel μ f hf y) := by
  have h := ae_all_iff.2 (fun n : ℕ =>
    factorConditionalKernel_map_smul_ae μ f hf hfi (denseSeq G n))
  filter_upwards [h] with y hy
  exact smulInvariantMeasure_of_denseRange _ (denseSeq G) (denseRange_denseSeq G) hy

variable {f hf}

/-- Almost every component of conditioning on all invariant sets is invariant. -/
theorem invariantConditionalMeasures_invariant_ae :
    ∀ᵐ x ∂μ, SMulInvariantMeasure G X (invariantConditionalMeasures (G := G) μ x) := by
  change ∀ᵐ x ∂μ, SMulInvariantMeasure G X
    (factorConditionalKernel μ (invariantFactorMap G X)
      (measurable_invariantFactorMap G X) (invariantFactorMap G X x))
  apply ae_of_ae_map (μ := μ)
    (p := fun y => SMulInvariantMeasure G X
      (factorConditionalKernel μ (invariantFactorMap G X) (measurable_invariantFactorMap G X) y))
    (measurable_invariantFactorMap G X).aemeasurable
  apply factorConditionalKernel_invariant_ae_dense μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X)
  intro g s hs x
  have hm : @Measurable X (InvariantFactor G X) (invariantSigma G X) _
      (invariantFactorMap G X) := by
    rw [measurable_iff_comap_le]
    change ((invariantSigma G X).comap InvariantFactor.val).comap (invariantFactorMap G X) ≤ _
    rw [MeasurableSpace.comap_comp]
    change (invariantSigma G X).comap id ≤ _
    rw [MeasurableSpace.comap_id]
  have he := ((measurableSet_invariantSigma G X).mp (hm hs)).2 g
  exact Iff.of_eq (congrArg (fun t : Set X => x ∈ t) he)

end PolycyclicRecognition

end

end OAI
