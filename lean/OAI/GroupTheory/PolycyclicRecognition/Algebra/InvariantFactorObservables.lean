import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConditionalKernelAlmostEverywhere

namespace OAI

/-! # Observable and almost-everywhere identities on invariant components -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set

variable {G X Z : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableSpace Z]

theorem measurable_invariantFactor_lift (F : X → Z) (hF : Measurable F)
    (hi : ∀ (g : G) x, F (g • x) = F x) :
    Measurable (fun y : InvariantFactor G X => F y.val) := by
  intro s hs
  change ∃ t, @MeasurableSet X (invariantSigma G X) t ∧
    InvariantFactor.val ⁻¹' t = (fun y : InvariantFactor G X => F y.val) ⁻¹' s
  refine ⟨F ⁻¹' s, (measurableSet_invariantSigma G X).2 ⟨hF hs, ?_⟩, rfl⟩
  intro g
  ext x
  simp only [mem_preimage, hi]

theorem invariantFactor_membership_smul (g : G) (s : Set (InvariantFactor G X))
    (hs : MeasurableSet s) (x : X) :
    invariantFactorMap G X (g • x) ∈ s ↔ invariantFactorMap G X x ∈ s := by
  have hm : @Measurable X (InvariantFactor G X) (invariantSigma G X) _
      (invariantFactorMap G X) := by
    rw [measurable_iff_comap_le]
    change ((invariantSigma G X).comap InvariantFactor.val).comap (invariantFactorMap G X) ≤ _
    rw [MeasurableSpace.comap_comp]
    change (invariantSigma G X).comap id ≤ _
    rw [MeasurableSpace.comap_id]
  have he := ((measurableSet_invariantSigma G X).mp (hm hs)).2 g
  exact Iff.of_eq (congrArg (fun t : Set X => x ∈ t) he)

variable [StandardBorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem invariantConditionalMeasures_ae {P : X → Prop}
    (hPm : MeasurableSet {x | P x}) (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂invariantConditionalMeasures (G := G) μ x, P y := by
  exact ae_of_ae_map (measurable_invariantFactorMap G X).aemeasurable
    (factorConditionalKernel_ae μ (invariantFactorMap G X)
      (measurable_invariantFactorMap G X) hPm hP)

theorem invariantConditionalMeasures_observable [MeasurableEq Z]
    (F : X → Z) (hF : Measurable F) (hi : ∀ (g : G) x, F (g • x) = F x) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂invariantConditionalMeasures (G := G) μ x, F y = F x := by
  exact ae_of_ae_map (measurable_invariantFactorMap G X).aemeasurable
    (factorConditionalKernel_fiber μ (invariantFactorMap G X)
      (measurable_invariantFactorMap G X) (fun y => F y.val)
      (measurable_invariantFactor_lift F hF hi))

theorem invariantConditionalMeasures_invariant_ae_countable [Countable G]
    [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] :
    ∀ᵐ x ∂μ, SMulInvariantMeasure G X (invariantConditionalMeasures (G := G) μ x) := by
  change ∀ᵐ x ∂μ, SMulInvariantMeasure G X
    (factorConditionalKernel μ (invariantFactorMap G X)
      (measurable_invariantFactorMap G X) (invariantFactorMap G X x))
  apply ae_of_ae_map (μ := μ)
    (p := fun y => SMulInvariantMeasure G X
      (factorConditionalKernel μ (invariantFactorMap G X) (measurable_invariantFactorMap G X) y))
    (measurable_invariantFactorMap G X).aemeasurable
  exact factorConditionalKernel_invariant_ae μ (invariantFactorMap G X)
    (measurable_invariantFactorMap G X) invariantFactor_membership_smul

end PolycyclicRecognition

end

end OAI
