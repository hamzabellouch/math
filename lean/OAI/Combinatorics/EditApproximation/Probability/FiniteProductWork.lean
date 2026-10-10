import OAI.Combinatorics.EditApproximation.Probability.RejectionSelectedCost

namespace OAI

/-! The executed sampler law supports both selected rejection work and
work depending only on the accepted finite draws. -/

namespace EditApproximation
open MeasureTheory

 theorem finite_outer_integrable {α β : Type*} [Fintype α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure β) [SFinite ν]
    (f : α × β → ℝ) (hsections : ∀ a, Integrable (fun b => f (a, b)) ν) :
    Integrable f (μ.prod ν) := by
  apply (integrable_prod_iff (measurable_of_countable f).aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall hsections, Integrable.of_finite⟩

 theorem finite_outer_expected_le {α β : Type*} [Fintype α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [SFinite ν]
    (f : α × β → ℝ) (hsections : ∀ a, Integrable (fun b => f (a, b)) ν)
    (budget : ℝ) (hbudget : ∀ a, (∫ b, f (a, b) ∂ν) ≤ budget) :
    (∫ outcome, f outcome ∂μ.prod ν) ≤ budget := by
  rw [integral_prod f (finite_outer_integrable μ ν f hsections)]
  calc
    _ ≤ ∫ _ : α, budget ∂μ := integral_mono Integrable.of_finite (integrable_const _) hbudget
    _ = _ := by simp

section Accepted
variable {α ι : Type*} [Fintype α] [Fintype ι]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (range : ι → ℕ) [∀ i, NeZero (range i)]
  (μ : Measure α) [IsFiniteMeasure μ]

 def rejectionProductAccepted (outcome : α × RejectionRuntimeArray range) : α × (∀ i, Fin (range i)) :=
  (outcome.1, outcome.2.2)

omit [Fintype α] [Fintype ι] [MeasurableSingletonClass α] [∀ i, NeZero (range i)] in
 theorem rejectionProductAccepted_measurable : Measurable (rejectionProductAccepted (α := α) range) :=
  measurable_fst.prodMk (measurable_snd.comp measurable_snd)

omit [MeasurableSingletonClass α] [IsFiniteMeasure μ] in
 theorem rejectionProductAccepted_law :
    (μ.prod (rejectionRuntimeArrayLaw range)).map (rejectionProductAccepted range) =
      μ.prod (rejectionAcceptedLaw range) := by
  change (μ.prod _).map (Prod.map id Prod.snd) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
    rejectionRuntimeArrayLaw_accepted]

omit [IsFiniteMeasure μ] in
 theorem rejectionProductWork_integral (f : α × (∀ i, Fin (range i)) → ℝ) :
    (∫ outcome, f (rejectionProductAccepted range outcome)
      ∂μ.prod (rejectionRuntimeArrayLaw range)) = ∫ outcome, f outcome ∂μ.prod (rejectionAcceptedLaw range) := by
  rw [← rejectionProductAccepted_law range μ]
  exact (integral_map (rejectionProductAccepted_measurable range).aemeasurable
    (measurable_of_finite f).aestronglyMeasurable).symm

omit [IsFiniteMeasure μ] in
 theorem rejectionProductWork_expected_le [IsProbabilityMeasure μ]
    (f : α × (∀ i, Fin (range i)) → ℝ) (budget : ℝ)
    (hbudget : ∀ draw, (∫ a, f (a, draw) ∂μ) ≤ budget) :
    (∫ outcome, f (rejectionProductAccepted range outcome)
      ∂μ.prod (rejectionRuntimeArrayLaw range)) ≤ budget := by
  rw [rejectionProductWork_integral range μ f, integral_prod_symm f Integrable.of_finite]
  calc
    _ ≤ ∫ _ : (∀ i, Fin (range i)), budget ∂rejectionAcceptedLaw range :=
      integral_mono Integrable.of_finite (integrable_const _) hbudget
    _ = _ := by simp

end Accepted
end EditApproximation

end OAI
