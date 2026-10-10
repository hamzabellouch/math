import OAI.MeasureTheory.DyadicAvoidance.AdaptiveLabels
import OAI.MeasureTheory.DyadicAvoidance.ExposureMoments
import OAI.MeasureTheory.DyadicAvoidance.CenterExposure
import OAI.MeasureTheory.DyadicAvoidance.SelectorMoment

namespace OAI

universe u_A u_I u_K u_C u_S u_T

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.FixedScaleProbability

/-- Exposing selector coordinates does not change the adaptive terminal-label
calculation: first restrict the selector measure, then integrate out terminals. -/
theorem measure_exposed_adaptive_failures_eq_lintegral
    {A : Type u_A} {I : Type u_I} {K : Type u_K} [MeasurableSpace A] [Fintype I] [Fintype K]
    (μ : Measure A) [SFinite μ] (ν : Measure Bool) [IsProbabilityMeasure ν]
    (E : Set A) (addr : A → I → K)
    (hinj : ∀ a, Function.Injective (addr a))
    (active : A → I → Prop) [∀ a i, Decidable (active a i)]
    (hmeas : MeasurableSet {z : A × (K → Bool) |
      ∀ i, active z.1 i → z.2 (addr z.1 i) = false}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → Bool) | z.1 ∈ E ∧
        ∀ i, active z.1 i → z.2 (addr z.1 i) = false} =
      ∫⁻ a in E, (ν {false}) ^ (Finset.univ.filter (active a)).card ∂μ := by
  have h := AdaptiveLabels.measure_adaptive_failures (μ.restrict E) ν
    addr hinj active hmeas
  rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply hmeas] at h
  convert h using 1
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod,
    Set.mem_univ, and_true]
  exact and_comm

/-- Fixed-scale failure on an exposure atom is its mass times the fresh-selector
moment. The selected terminal addresses may depend on every selector coordinate. -/
theorem measure_exposed_adaptive_failures
    {A : Type u_A} {I : Type u_I} {K : Type u_K} [MeasurableSpace A] [Fintype I] [Fintype K]
    (μ : Measure A) [SFinite μ] (ν : Measure Bool) [IsProbabilityMeasure ν]
    (E : Set A) (addr : A → I → K)
    (hinj : ∀ a, Function.Injective (addr a))
    (fresh : A → I → Bool) (hfresh : Measurable fresh)
    (σ : Measure (I → Bool))
    (hjoint : ∀ v, μ (E ∩ {a | fresh a = v}) = μ E * σ {v})
    (q : ENNReal)
    (hmoment : (∫⁻ v, (ν {false}) ^
      (Finset.univ.filter (fun i => v i = true)).card ∂σ) = q)
    (hmeas : MeasurableSet {z : A × (K → Bool) |
      ∀ i, fresh z.1 i = true → z.2 (addr z.1 i) = false}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → Bool) | z.1 ∈ E ∧
        ∀ i, fresh z.1 i = true → z.2 (addr z.1 i) = false} = μ E * q := by
  rw [measure_exposed_adaptive_failures_eq_lintegral μ ν E addr hinj
    (fun a i => fresh a i = true) hmeas]
  exact ExposureMoments.lintegral_restrict_comp_eq_of_fibers μ σ E fresh hfresh
    hjoint (fun v => (ν {false}) ^
      (Finset.univ.filter (fun i => v i = true)).card)
    (measurable_of_countable _) q hmoment

/-- Exact fixed-scale miss probability on a center-exposure atom. Selector
lookups are fair, fresh and pairwise distinct. Terminal addresses may depend
on all selectors, but their injectivity must hold for every selector outcome.
This is the finite-product version of the conditional estimate. -/
theorem measure_fixed_scale_on_center_atom
    {C : Type u_C} {I : Type u_I} {S : Type u_S} {T : Type u_T} [Fintype C] [Fintype I] [Fintype S] [Fintype T]
    (νs νt : Measure Bool) [IsProbabilityMeasure νs] [IsProbabilityMeasure νt]
    (hfalse : νs {false} = 1 / 2) (htrue : νs {true} = 1 / 2)
    (center : C → S) (fresh : I → S)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → Bool)
    (addr : (S → Bool) → I → T) (haddr : ∀ a, Function.Injective (addr a))
    (p : ℝ) (hp : p ≤ 1) (hterminal : νt {false} = ENNReal.ofReal (1 - p)) :
    ((Measure.pi (fun _ : S => νs)).prod (Measure.pi (fun _ : T => νt)))
      {z : (S → Bool) × (T → Bool) |
        (∀ c, z.1 (center c) = value c) ∧
        ∀ i, z.1 (fresh i) = true → z.2 (addr z.1 i) = false} =
      (∏ c, νs {value c}) * (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by
  classical
  have hcalc := measure_exposed_adaptive_failures_eq_lintegral
    (Measure.pi (fun _ : S => νs)) νt
    {a | ∀ c, a (center c) = value c} addr haddr
    (fun a i => a (fresh i) = true) MeasurableSet.of_discrete
  simp only [Set.mem_ofPred_eq] at hcalc
  rw [hcalc]
  have hmoment := CenterExposure.lintegral_fresh_restrict_center_atom
    νs center fresh hinj value
    (fun v => (νt {false}) ^ (Finset.univ.filter (fun i => v i = true)).card)
    (measurable_of_countable _)
  rw [hmoment]
  congr 1
  rw [hterminal]
  simpa only [Fintype.card_subtype, id_eq] using
    SelectorMoment.lookup_fair_failure_moment νs hfalse htrue
      (id : I → I) Function.injective_id p hp

/-- The preceding identity with the actual center-atom mass as coefficient,
ready for summation over center exposure values. -/
theorem measure_fixed_scale_eq_atom_mass
    {C : Type u_C} {I : Type u_I} {S : Type u_S} {T : Type u_T} [Fintype C] [Fintype I] [Fintype S] [Fintype T]
    (νs νt : Measure Bool) [IsProbabilityMeasure νs] [IsProbabilityMeasure νt]
    (hfalse : νs {false} = 1 / 2) (htrue : νs {true} = 1 / 2)
    (center : C → S) (fresh : I → S)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → Bool)
    (addr : (S → Bool) → I → T) (haddr : ∀ a, Function.Injective (addr a))
    (p : ℝ) (hp : p ≤ 1) (hterminal : νt {false} = ENNReal.ofReal (1 - p)) :
    ((Measure.pi (fun _ : S => νs)).prod (Measure.pi (fun _ : T => νt)))
      {z : (S → Bool) × (T → Bool) |
        (∀ c, z.1 (center c) = value c) ∧
        ∀ i, z.1 (fresh i) = true → z.2 (addr z.1 i) = false} =
      (Measure.pi (fun _ : S => νs)) {a | ∀ c, a (center c) = value c} *
        (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by
  rw [measure_fixed_scale_on_center_atom νs νt hfalse htrue
    center fresh hinj value addr haddr p hp hterminal]
  congr 1
  have hcenter : Function.Injective center := by
    intro c d h
    exact Sum.inl.inj (hinj (show Sum.elim center fresh (Sum.inl c) =
      Sum.elim center fresh (Sum.inl d) from h))
  symm
  simpa only [Set.mem_singleton_iff] using
    AdaptiveLabels.measure_injective_constraints νs center hcenter
      (fun c => {value c}) (fun c => measurableSet_singleton (value c))

end Problem310.FixedScaleProbability

end OAI
