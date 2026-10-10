import Mathlib

namespace OAI

universe u_I u_K u_B u_A

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.AdaptiveLabels

/-- Distinct table addresses read independent labels, including when some
addresses in the table are unused. -/
theorem measure_injective_constraints
    {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype I] [Fintype K] [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (addr : I → K) (hinj : Function.Injective addr)
    (s : I → Set B) (hs : ∀ i, MeasurableSet (s i)) :
    (Measure.pi (fun _ : K => ν)) {ω | ∀ i, ω (addr i) ∈ s i} =
      ∏ i, ν (s i) := by
  classical
  have hind : iIndepFun (fun k (ω : K → B) => ω k)
      (Measure.pi (fun _ : K => ν)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h := (hind.precomp hinj).measure_inter_preimage_eq_mul
    Finset.univ (fun i _ => hs i)
  simp only [Finset.mem_univ, Set.iInter_true] at h
  rw [show {ω : K → B | ∀ i, ω (addr i) ∈ s i} =
    (⋂ i, (fun ω : K → B => ω (addr i)) ⁻¹' s i) by ext ω; simp]
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  exact (measurePreserving_eval (fun _ : K => ν) (addr i)).measure_preimage
    (hs i).nullMeasurableSet

/-- An address choice may depend arbitrarily on a separate selector outcome.
After fixing that outcome, injectivity is the only required terminal-table fact. -/
theorem measure_adaptive_constraints
    {A : Type u_A} {I : Type u_I} {K : Type u_K} {B : Type u_B} [MeasurableSpace A] [Fintype I] [Fintype K]
    [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure ν]
    (addr : A → I → K) (hinj : ∀ a, Function.Injective (addr a))
    (s : A → I → Set B) (hs : ∀ a i, MeasurableSet (s a i))
    (hmeas : MeasurableSet {z : A × (K → B) |
      ∀ i, z.2 (addr z.1 i) ∈ s z.1 i}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → B) | ∀ i, z.2 (addr z.1 i) ∈ s z.1 i} =
      ∫⁻ a, ∏ i, ν (s a i) ∂μ := by
  rw [Measure.prod_apply hmeas]
  apply lintegral_congr
  intro a
  exact measure_injective_constraints ν (addr a) (hinj a) (s a) (hs a)

/-- The conditional failure probability of adaptively addressed Boolean tests.
Only active tests impose a zero label; distinct active addresses suffice here
because we assume the stronger, routing-friendly injectivity of all addresses. -/
theorem measure_adaptive_failures
    {A : Type u_A} {I : Type u_I} {K : Type u_K} [MeasurableSpace A] [Fintype I] [Fintype K]
    (μ : Measure A) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → I → K) (hinj : ∀ a, Function.Injective (addr a))
    (active : A → I → Prop) [∀ a i, Decidable (active a i)]
    (hmeas : MeasurableSet {z : A × (K → Bool) |
      ∀ i, active z.1 i → z.2 (addr z.1 i) = false}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → Bool) | ∀ i, active z.1 i → z.2 (addr z.1 i) = false} =
      ∫⁻ a, (ν {false}) ^ (Finset.univ.filter (active a)).card ∂μ := by
  classical
  let s : A → I → Set Bool := fun a i => if active a i then {false} else Set.univ
  have hset : {z : A × (K → Bool) |
      ∀ i, active z.1 i → z.2 (addr z.1 i) = false} =
      {z : A × (K → Bool) | ∀ i, z.2 (addr z.1 i) ∈ s z.1 i} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    apply forall_congr'
    intro i
    by_cases h : active z.1 i <;> simp [s, h]
  rw [hset] at hmeas ⊢
  rw [measure_adaptive_constraints μ ν addr hinj s
    (fun _ _ => MeasurableSet.of_discrete) hmeas]
  apply lintegral_congr
  intro a
  simp only [s, apply_ite, measure_univ]
  simp [Finset.prod_ite]

/-- Looking up one terminal label at a selector-dependent address preserves its
marginal law. This is the pointwise mean-density identity for the routed set. -/
theorem measure_adaptive_label
    {A : Type u_A} {K : Type u_K} {B : Type u_B} [MeasurableSpace A] [Fintype K]
    [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (addr : A → K) (s : Set B) (hs : MeasurableSet s)
    (hmeas : MeasurableSet {z : A × (K → B) | z.2 (addr z.1) ∈ s}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → B) | z.2 (addr z.1) ∈ s} = ν s := by
  have h := measure_adaptive_constraints (I := Unit) μ ν
    (fun a _ => addr a) (fun _ _ _ _ => Subsingleton.elim _ _)
    (fun _ _ => s) (fun _ _ => hs) (by simpa using hmeas)
  simpa using h

end Problem310.AdaptiveLabels

end OAI
