import OAI.MeasureTheory.DyadicAvoidance.AdaptiveLabels

namespace OAI

universe u_C u_I u_K u_B

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Problem310.CenterExposure

/-- Center and fresh addresses together are injective if each family is
injective and their coordinate ranges are disjoint. -/
theorem injective_sum_addresses {C : Type u_C} {I : Type u_I} {K : Type u_K}
    (center : C → K) (fresh : I → K)
    (hc : Function.Injective center) (hf : Function.Injective fresh)
    (hdisj : ∀ c i, center c ≠ fresh i) :
    Function.Injective (Sum.elim center fresh) := by
  intro a b hab
  cases a with
  | inl c =>
      cases b with
      | inl d => exact congrArg Sum.inl (hc hab)
      | inr i => exact False.elim (hdisj c i hab)
  | inr i =>
      cases b with
      | inl c => exact False.elim (hdisj c i hab.symm)
      | inr j => exact congrArg Sum.inr (hf hab)

/-- Center constraints do not alter the product law of distinct fresh
coordinates. This unnormalized identity avoids all conditional-expectation
bookkeeping and applies to arbitrary coordinate label spaces. -/
theorem measure_center_and_fresh
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K]
    [MeasurableSpace B] (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh))
    (s : C → Set B) (t : I → Set B)
    (hs : ∀ c, MeasurableSet (s c)) (ht : ∀ i, MeasurableSet (t i)) :
    (Measure.pi (fun _ : K => ν))
      {ω | (∀ c, ω (center c) ∈ s c) ∧ (∀ i, ω (fresh i) ∈ t i)} =
      (∏ c, ν (s c)) * ∏ i, ν (t i) := by
  have h := AdaptiveLabels.measure_injective_constraints ν
    (Sum.elim center fresh) hinj (Sum.elim s t) (by
      intro k
      cases k with
      | inl c => exact hs c
      | inr i => exact ht i)
  simpa only [Sum.forall, Sum.elim_inl, Sum.elim_inr,
    Fintype.prod_sum_type] using h

/-- Specialization to an atom specifying all exposed center entries. -/
theorem measure_center_atom_and_fresh
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh))
    (value : C → B) (t : I → Set B)
    (ht : ∀ i, MeasurableSet (t i)) :
    (Measure.pi (fun _ : K => ν))
      {ω | (∀ c, ω (center c) = value c) ∧ (∀ i, ω (fresh i) ∈ t i)} =
      (∏ c, ν {value c}) * ∏ i, ν (t i) := by
  simpa only [Set.mem_singleton_iff] using
    measure_center_and_fresh ν center fresh hinj (fun c => {value c}) t
      (fun c => measurableSet_singleton (value c)) ht

/-- The whole fresh coordinate vector has its original product law after
restricting to a center atom, multiplied only by the atom's mass. This
form permits arbitrary fresh-vector events and moments, not just cylinders. -/
theorem map_fresh_restrict_center_atom
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K] [Countable B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → B) :
    Measure.map (fun ω : K → B => fun i => ω (fresh i))
      ((Measure.pi (fun _ : K => ν)).restrict
        {ω | ∀ c, ω (center c) = value c}) =
      (∏ c, ν {value c}) • Measure.pi (fun _ : I => ν) := by
  have hg : Measurable (fun ω : K → B => fun i => ω (fresh i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (fresh i))
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply hg (measurableSet_singleton v),
    Measure.restrict_apply (hg (measurableSet_singleton v))]
  have heq :
      (fun ω : K → B => fun i => ω (fresh i)) ⁻¹' {v} ∩
        {ω | ∀ c, ω (center c) = value c} =
      {ω : K → B | (∀ c, ω (center c) = value c) ∧
        (∀ i, ω (fresh i) ∈ ({v i} : Set B))} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, funext_iff]
    exact and_comm
  rw [heq, measure_center_atom_and_fresh ν center fresh hinj value
    (fun i => {v i}) (fun i => measurableSet_singleton (v i))]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_singleton]

/-- Any nonnegative measurable function of the fresh vector has the same
moment on a center atom, up to multiplication by the atom mass. -/
theorem lintegral_fresh_restrict_center_atom
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K] [Countable B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → B)
    (F : (I → B) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, F (fun i => ω (fresh i)) ∂
      ((Measure.pi (fun _ : K => ν)).restrict
        {ω | ∀ c, ω (center c) = value c})) =
      (∏ c, ν {value c}) * ∫⁻ v, F v ∂Measure.pi (fun _ : I => ν) := by
  have hg : Measurable (fun ω : K → B => fun i => ω (fresh i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (fresh i))
  rw [← lintegral_map hF hg, map_fresh_restrict_center_atom ν center fresh hinj value,
    lintegral_smul_measure, smul_eq_mul]

end Problem310.CenterExposure

end

end OAI
