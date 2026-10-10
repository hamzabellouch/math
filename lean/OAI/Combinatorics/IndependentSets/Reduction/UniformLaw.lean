import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.ScalarCell

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

instance cubeMeasurable (m : ℕ) : MeasurableSpace (Cube m) := ⊤
instance cubeSingleton (m : ℕ) : MeasurableSingletonClass (Cube m) := ⟨fun _ => trivial⟩

noncomputable def uniformLaw (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] : Measure α :=
  (PMF.uniformOfFintype α).toMeasure

instance uniformLaw_probability (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] :
    IsProbabilityMeasure (uniformLaw α) := by unfold uniformLaw; infer_instance

lemma integral_uniformLaw {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (g : α → ℝ) :
    (∫ x, g x ∂uniformLaw α) = 𝔼 x, g x := by
  rw [integral_fintype Integrable.of_finite]
  simp only [uniformLaw, measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    Finset.expect_eq_sum_div_card, Finset.card_univ, ← Finset.mul_sum]
  ring

noncomputable def unitLaw : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)

instance unitLaw_probability : IsProbabilityMeasure unitLaw := by
  constructor
  norm_num [unitLaw, Measure.restrict_apply_univ]

lemma integral_unitLaw (g : ℝ → ℝ) : (∫ x, g x ∂unitLaw) = ∫ x in (0:ℝ)..1, g x := by
  rw [unitLaw, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]

noncomputable def scalarSampler (m : ℕ) (p : Cube m × ℝ) : ℝ := scalarCell p.1 p.2

lemma scalarSampler_measurable (m : ℕ) : Measurable (scalarSampler m) :=
  measurable_from_prod_countable_right (fun q => (scalarCell_lipschitz q).continuous.measurable)

theorem scalarSampler_preserving (m : ℕ) :
    MeasurePreserving (scalarSampler m) ((uniformLaw (Cube m)).prod unitLaw) unitLaw := by
  refine ⟨scalarSampler_measurable m, ?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have mf : AEStronglyMeasurable (fun x => f x)
      (Measure.map (scalarSampler m) ((uniformLaw (Cube m)).prod unitLaw)) :=
    f.continuous.stronglyMeasurable.aestronglyMeasurable
  rw [integral_map (scalarSampler_measurable m).aemeasurable mf]
  have hi : Integrable (fun p => f (scalarSampler m p)) ((uniformLaw (Cube m)).prod unitLaw) := by
    apply Integrable.of_bound
      ((f.continuous.measurable.comp (scalarSampler_measurable m)).stronglyMeasurable.aestronglyMeasurable)
      ‖f.toBoundedContinuousFunction‖
    filter_upwards [] with x
    exact f.toBoundedContinuousFunction.norm_coe_le_norm _
  rw [integral_prod _ hi, integral_uniformLaw]
  simp only [scalarSampler, integral_unitLaw]
  exact mean_scalarAvg f.continuous

end LargeIndependentSets.BooleanJunta

end OAI
