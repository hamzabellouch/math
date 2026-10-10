import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace OAI

/-!
# Precommitted finite conditional-kernel tables

The secretary reconstruction may be implemented with no randomness drawn after
arrivals: draw one independent kernel output for every possible finite observation
before arrivals, and later read only the entry indexed by the observation. The
entire table, including unused entries, is part of the initial seed.

These lemmas establish the law of that concrete construction. They do not assert
independence after conditioning on the entire table, and do not assume a secretary
transport theorem or a reward guarantee.
-/

namespace MatroidProphet.PrecommittedKernel

open MeasureTheory

variable {I A : Type*} [Fintype I] [Fintype A]
  [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSingletonClass A] in
/-- Reading one fixed coordinate from the initial table has the prescribed law. -/
theorem map_eval (κ : I → Measure A) [∀ i, IsProbabilityMeasure (κ i)] (i : I) :
    Measure.map (fun q : I → A => q i) (Measure.pi κ) = κ i :=
  (measurePreserving_eval κ i).map_eq

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- Every statistic of one kernel output has the same expectation under the
precommitted table construction. No later draw is needed. -/
theorem integral_eval (κ : I → Measure A) [∀ i, IsProbabilityMeasure (κ i)]
    (i : I) (f : A → ℝ) :
    (∫ q : I → A, f (q i) ∂Measure.pi κ) = ∫ a, f a ∂κ i := by
  have h := integral_map (μ := Measure.pi κ)
    (measurable_pi_apply i).aemeasurable (measurable_of_countable f).aestronglyMeasurable
  rw [map_eval κ i] at h
  exact h.symm

/-- An observation independent of the whole initial table selects exactly its
conditional kernel. The function may depend jointly on observation and output. -/
theorem integral_joint (μ : Measure I) [IsFiniteMeasure μ]
    (κ : I → Measure A) [∀ i, IsProbabilityMeasure (κ i)] (f : I → A → ℝ) :
    (∫ z : I × (I → A), f z.1 (z.2 z.1) ∂μ.prod (Measure.pi κ)) =
      ∫ i, ∫ a, f i a ∂κ i ∂μ := by
  rw [integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun i => integral_eval κ i (f i)

/-- Exact joint atom law, retaining the observation as well as reconstructed
output. This is stronger than only identifying the output marginal. -/
theorem joint_singleton (μ : Measure I) [IsFiniteMeasure μ]
    (κ : I → Measure A) [∀ i, IsProbabilityMeasure (κ i)] (i : I) (a : A) :
    Measure.map (fun z : I × (I → A) => (z.1, z.2 z.1))
      (μ.prod (Measure.pi κ)) {(i, a)} = μ {i} * κ i {a} := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : (fun z : I × (I → A) => (z.1, z.2 z.1)) ⁻¹' {(i, a)} =
      {i} ×ˢ ((fun q : I → A => q i) ⁻¹' {a}) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
      Set.mem_prod]
    constructor
    · rintro ⟨hi, ha⟩
      exact ⟨hi, by simpa [hi] using ha⟩
    · rintro ⟨hi, ha⟩
      exact ⟨hi, by simpa [hi] using ha⟩
  rw [hpre, Measure.prod_prod]
  congr 1
  have h := congrArg (fun ν : Measure A => ν {a}) (map_eval κ i)
  rw [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton a)] at h
  exact h

/-- A candidate joint law is recovered exactly if its atoms have the specified
observation marginal times conditional kernel law. All unused table coordinates
remain present in the concrete initial probability space. -/
theorem map_joint_eq (μ : Measure I) [IsFiniteMeasure μ]
    (κ : I → Measure A) [∀ i, IsProbabilityMeasure (κ i)] (ν : Measure (I × A))
    (hν : ∀ i a, ν {(i, a)} = μ {i} * κ i {a}) :
    Measure.map (fun z : I × (I → A) => (z.1, z.2 z.1))
      (μ.prod (Measure.pi κ)) = ν := by
  apply Measure.ext_of_singleton
  rintro ⟨i, a⟩
  exact (joint_singleton μ κ i a).trans (hν i a).symm

/-- The observation may itself be any measurable function of a separate random
experiment (for example a binomial cutoff and uniform arrival permutation).
Only its marginal law matters to the precommitted-table reconstruction. -/
theorem map_random_index {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (X : Ω → I) (hX : Measurable X)
    (κ : I → Measure A) [∀ i, IsProbabilityMeasure (κ i)] :
    Measure.map (fun z : Ω × (I → A) => (X z.1, z.2 (X z.1)))
      (μ.prod (Measure.pi κ)) =
    Measure.map (fun z : I × (I → A) => (z.1, z.2 z.1))
      ((Measure.map X μ).prod (Measure.pi κ)) := by
  have hp := Measure.map_prod_map μ (Measure.pi κ) hX measurable_id
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map (measurable_of_countable _) (hX.prodMap measurable_id)]
  rfl

section Dependent

variable {B : I → Type*} [∀ i, Fintype (B i)]
  [∀ i, MeasurableSpace (B i)] [∀ i, MeasurableSingletonClass (B i)]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- Dependent kernel tables allow the output type at each observation to be its
valid fiber. Thus every initial table, including null-probability tables, obeys
the reconstruction constraint by type, rather than only almost surely. -/
theorem integral_eval_dependent (κ : (i : I) → Measure (B i))
    [∀ i, IsProbabilityMeasure (κ i)] (i : I) (f : B i → ℝ) :
    (∫ q : (i : I) → B i, f (q i) ∂Measure.pi κ) = ∫ a, f a ∂κ i := by
  have h := integral_map (μ := Measure.pi κ)
    (measurable_pi_apply i).aemeasurable (measurable_of_countable f).aestronglyMeasurable
  rw [(measurePreserving_eval κ i).map_eq] at h
  exact h.symm

/-- Exact conditional expectation for dependent-fiber precommitted tables. -/
theorem integral_joint_dependent (μ : Measure I) [IsFiniteMeasure μ]
    (κ : (i : I) → Measure (B i)) [∀ i, IsProbabilityMeasure (κ i)]
    (f : (i : I) → B i → ℝ) :
    (∫ z : I × ((i : I) → B i), f z.1 (z.2 z.1) ∂μ.prod (Measure.pi κ)) =
      ∫ i, ∫ a, f i a ∂κ i ∂μ := by
  rw [integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun i => integral_eval_dependent κ i (f i)

end Dependent

end MatroidProphet.PrecommittedKernel

end OAI
