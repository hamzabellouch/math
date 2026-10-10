import OAI.Analysis.FiniteFactor.FiniteProductAbsoluteContinuity
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal
noncomputable section

/-- Equal-weight mixture of two probability measures. -/
def probabilityAverage {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : Measure X :=
  (2 : ℝ≥0∞)⁻¹ • (μ + ν)

instance probabilityAverage_probability {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (probabilityAverage μ ν) := by
  constructor
  simpa [probabilityAverage,Measure.smul_apply,Measure.add_apply,measure_univ]
    using ENNReal.inv_two_add_inv_two

/-- A single-coordinate update, as a linear operation on the remaining law. -/
def coordinateUpdateLaw {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (i : ι) (μ : Measure X) (ν : Measure (ι → X)) : Measure (ι → X) :=
  (μ.prod ν).map (fun z : X × (ι → X) => Function.update z.2 i z.1)

theorem measurable_coordinateUpdate {ι X : Type*} [DecidableEq ι] [MeasurableSpace X] (i : ι) :
    Measurable (fun z : X × (ι → X) => Function.update z.2 i z.1) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : k = i
  · subst k; simpa using (measurable_fst : Measurable (Prod.fst : X × (ι → X) → X))
  · simpa [Function.update_of_ne hk,Function.comp_def] using (measurable_pi_apply k).comp
      (measurable_snd : Measurable (Prod.snd : X × (ι → X) → (ι → X)))

theorem coordinateUpdateLaw_add_right {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (i : ι) (μ : Measure X) (ν η : Measure (ι → X))
    [SFinite μ] [SFinite ν] [SFinite η] :
    coordinateUpdateLaw i μ (ν+η) = coordinateUpdateLaw i μ ν + coordinateUpdateLaw i μ η := by
  rw [coordinateUpdateLaw,Measure.prod_add,Measure.map_add _ _ (measurable_coordinateUpdate i)]
  rfl

theorem coordinateUpdateLaw_average {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (i : ι) (μ ν : Measure X) (η : Measure (ι → X))
    [SFinite μ] [SFinite ν] [SFinite η] :
    coordinateUpdateLaw i (probabilityAverage μ ν) η =
      (2 : ℝ≥0∞)⁻¹ • (coordinateUpdateLaw i μ η + coordinateUpdateLaw i ν η) := by
  unfold coordinateUpdateLaw probabilityAverage
  rw [Measure.prod_smul_left,Measure.add_prod,
    Measure.map_smul _ (measurable_coordinateUpdate i).aemeasurable,
    Measure.map_add _ _ (measurable_coordinateUpdate i)]

end
end FiniteFactor

end OAI
