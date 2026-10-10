import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import OAI.Probability.MatroidSecretary.Secretary.SourcePrefixLaw
import OAI.Probability.MatroidSecretary.Secretary.Precommit
import OAI.Probability.MatroidSecretary.Weights.FiniteWeightLawTheorems
import OAI.Probability.MatroidSecretary.Secretary.ConditionalLaw
import OAI.Probability.MatroidProphet.Main
import OAI.Probability.MatroidSecretary.Secretary.PrefixObservationModel
import OAI.Probability.MatroidSecretary.Secretary.ProbabilityModel

namespace OAI

/-!
# Initial-seed / random-prefix coupling

The complete table is drawn with the initial seed, before the independent
arrival permutation.  Reassociation here is only a proof of the joint law;
the implementation does not defer any table randomness until after the prefix.
-/

namespace MatroidProphet.Secretary

open MeasureTheory

variable {U T S B A : Type*}
variable [MeasurableSpace U] [MeasurableSpace T] [MeasurableSpace S]
variable [MeasurableSpace B] [MeasurableSpace A]

/-- Moving the independent arrival randomness next to the source seed does not
change the product law; the entire precommitted table remains present. -/
theorem initial_seed_reassociate (μ : Measure U) (ν : Measure T) (η : Measure S)
    [SFinite μ] [SFinite ν] [SFinite η] :
    MeasurePreserving (fun z : (U × T) × S => ((z.1.1, z.2), z.1.2))
      ((μ.prod ν).prod η) ((μ.prod η).prod ν) := by
  have h₁ := measurePreserving_prodAssoc μ ν η
  have h₂ := (MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := ν) (ν := η))
  have h₃ := (measurePreserving_prodAssoc μ η ν).symm MeasurableEquiv.prodAssoc
  exact h₃.comp (h₂.comp h₁)

/-- Any observation of source seed and independent prefix randomness retains
independence from the complete pre-drawn table. -/
theorem observation_table_joint (μ : Measure U) (ν : Measure T) (η : Measure S)
    (ρ : Measure B) [SFinite μ] [SFinite ν] [SFinite η]
    (index : U × S → B) (hi : Measurable index)
    (hindex : (μ.prod η).map index = ρ) :
    ((μ.prod ν).prod η).map
      (fun z : (U × T) × S => (index (z.1.1, z.2), z.1.2)) = ρ.prod ν := by
  have hm : MeasurePreserving index (μ.prod η) ρ := ⟨hi, hindex⟩
  exact ((hm.prod (MeasurePreserving.id ν)).comp
    (initial_seed_reassociate μ ν η)).map_eq

/-- Decoding the precommitted table after observing the prefix has the same
law as selecting from an independent table at an index with the required
observation law.  No future arrival information is an input to `decode`. -/
theorem reconstructed_seed_law (μ : Measure U) (ν : Measure T) (η : Measure S)
    (ρ : Measure B) (ξ : Measure A) [SFinite μ] [SFinite ν] [SFinite η]
    (index : U × S → B) (hi : Measurable index)
    (hindex : (μ.prod η).map index = ρ)
    (decode : B × T → A) (hd : Measurable decode)
    (hdecode : (ρ.prod ν).map decode = ξ) :
    ((μ.prod ν).prod η).map
      (fun z : (U × T) × S => decode (index (z.1.1, z.2), z.1.2)) = ξ := by
  rw [← hdecode, ← observation_table_joint μ ν η ρ index hi hindex,
    Measure.map_map hd]
  · rfl
  · exact (hi.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.snd

end MatroidProphet.Secretary

namespace MatroidProphet.Secretary

open MeasureTheory

variable {A B : Type*} [Fintype A] [Fintype B]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable [MeasurableSpace B] [MeasurableSingletonClass B]
variable [DecidableEq A] [DecidableEq B]

/-- Normalize the actual source measure on each observation fiber. -/
noncomputable def conditionalSourceLaw (μ : Measure A) (obs : A → B)
    (fallback : A) (b : B) : Measure A :=
  FiniteLaw.weightMeasure
    (fiberKernel (fun a => μ.real {a}) obs fallback b)
    (fiberKernel_nonneg _ (fun _ => measureReal_nonneg) obs fallback b)
    (fiberKernel_sum _ obs fallback b)

instance conditionalSourceLaw_probability (μ : Measure A) (obs : A → B)
    (fallback : A) (b : B) : IsProbabilityMeasure (conditionalSourceLaw μ obs fallback b) := by
  unfold conditionalSourceLaw
  infer_instance

omit [Fintype B] [DecidableEq A] in
/-- The graph of the observation keeps the full source realization. -/
theorem observation_graph_atom (μ : Measure A) (obs : A → B) (b : B) (a : A) :
    (μ.map (fun a => (obs a, a))) {(b, a)} =
      if obs a = b then μ {a} else 0 := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have heq : (fun a => (obs a, a)) ⁻¹' {(b, a)} =
      if obs a = b then {a} else ∅ := by
    by_cases hobs : obs a = b
    · rw [ite_eq_left hobs]
      ext source
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨hobs, rfl⟩
    · rw [ite_eq_right hobs]
      ext source
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨hvalue, rfl⟩
      exact hobs hvalue
  rw [heq]
  split_ifs <;> simp

omit [Fintype B] in
/-- The true observation marginal times the normalized conditional law is the
exact graph law of the complete source seed, including unused coordinates. -/
theorem conditionalSourceLaw_joint_atom (μ : Measure A) [IsProbabilityMeasure μ]
    (obs : A → B) (fallback : A) (b : B) (a : A) :
    (μ.map obs) {b} * conditionalSourceLaw μ obs fallback b {a} =
      (μ.map (fun a => (obs a, a))) {(b, a)} := by
  have hmap : (μ.map obs) {b} =
      ENNReal.ofReal (fiberMass (fun a => μ.real {a}) obs b) := by
    calc
      _ = ENNReal.ofReal ((μ.map obs).real {b}) :=
        (ENNReal.ofReal_toReal (measure_ne_top (μ.map obs) {b})).symm
      _ = _ := congrArg ENNReal.ofReal (by
        rw [FiniteLaw.map_real_singleton]
        unfold fiberMass
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : obs a = b <;> simp [h])
  rw [hmap, conditionalSourceLaw, FiniteLaw.weightMeasure_singleton,
    ← ENNReal.ofReal_mul (fiberMass_nonneg _ (fun _ => measureReal_nonneg) obs b),
    fiberMass_mul_fiberKernel _ (fun _ => measureReal_nonneg) obs fallback,
    observation_graph_atom]
  split_ifs
  · exact ENNReal.ofReal_toReal (measure_ne_top μ {a})
  · simp

/-- Predrawing every conditional source seed and selecting the observed fiber
reconstructs the complete source joint law exactly. -/
theorem conditional_table_joint (μ : Measure A) [IsProbabilityMeasure μ]
    (obs : A → B) (fallback : A) :
    ((μ.map obs).prod (Measure.pi (conditionalSourceLaw μ obs fallback))).map
      (fun z : B × (B → A) => (z.1, z.2 z.1)) =
      μ.map (fun a => (obs a, a)) := by
  apply SecretaryPrecommit.selected_joint_eq
  intro b a
  exact (conditionalSourceLaw_joint_atom μ obs fallback b a).symm

/-- The actual initial seed is `(source seed, whole conditional table)`,
independent of prefix randomness.  If the prefix observation has the true
observation law, lookup recovers the full joint source law. -/
theorem precommitted_source_joint {S : Type*} [MeasurableSpace S]
    (μ : Measure A) [IsProbabilityMeasure μ] (η : Measure S) [SFinite η]
    (obs : A → B) (fallback : A) (index : A × S → B)
    (hi : Measurable index) (hindex : (μ.prod η).map index = μ.map obs) :
    ((μ.prod (Measure.pi (conditionalSourceLaw μ obs fallback))).prod η).map
      (fun z : (A × (B → A)) × S =>
        (index (z.1.1, z.2), z.1.2 (index (z.1.1, z.2)))) =
      μ.map (fun a => (obs a, a)) := by
  exact reconstructed_seed_law μ (Measure.pi (conditionalSourceLaw μ obs fallback)) η
    (μ.map obs) (μ.map (fun a => (obs a, a))) index hi hindex
    (fun z : B × (B → A) => (z.1, z.2 z.1)) (measurable_of_countable _)
    (conditional_table_joint μ obs fallback)

/-- In particular the reconstructed seed, with all unused coordinates, has
the original source marginal. -/
theorem precommitted_source_marginal {S : Type*} [MeasurableSpace S]
    (μ : Measure A) [IsProbabilityMeasure μ] (η : Measure S) [SFinite η]
    (obs : A → B) (fallback : A) (index : A × S → B)
    (hi : Measurable index) (hindex : (μ.prod η).map index = μ.map obs) :
    ((μ.prod (Measure.pi (conditionalSourceLaw μ obs fallback))).prod η).map
      (fun z : (A × (B → A)) × S => z.1.2 (index (z.1.1, z.2))) = μ := by
  have h := congrArg (fun ν : Measure (B × A) => ν.map Prod.snd)
    (precommitted_source_joint μ η obs fallback index hi hindex)
  have hf : Measurable (fun z : (A × (B → A)) × S =>
      (index (z.1.1, z.2), z.1.2 (index (z.1.1, z.2)))) :=
    (measurable_of_countable (fun z : B × (B → A) => (z.1, z.2 z.1))).comp
      ((hi.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd)
  rw [Measure.map_map measurable_snd hf,
    Measure.map_map measurable_snd (measurable_of_countable _)] at h
  change ((μ.prod (Measure.pi (conditionalSourceLaw μ obs fallback))).prod η).map
    (fun z : (A × (B → A)) × S => z.1.2 (index (z.1.1, z.2))) = μ.map id at h
  simpa only [Measure.map_id] using h

theorem ae_precommitted_source_observation {S : Type*} [MeasurableSpace S]
    (μ : Measure A) [IsProbabilityMeasure μ] (η : Measure S) [SFinite η]
    (obs : A → B) (fallback : A) (index : A × S → B)
    (hi : Measurable index) (hindex : (μ.prod η).map index = μ.map obs) :
    ∀ᵐ z : (A × (B → A)) × S
      ∂(μ.prod (Measure.pi (conditionalSourceLaw μ obs fallback))).prod η,
      obs (z.1.2 (index (z.1.1, z.2))) = index (z.1.1, z.2) := by
  have hgraph : ∀ᵐ x : B × A ∂μ.map (fun a => (obs a, a)), obs x.2 = x.1 := by
    exact (ae_map_iff (measurable_of_countable _).aemeasurable
      (Set.to_countable _).measurableSet).2 (ae_of_all _ fun _ => rfl)
  rw [← precommitted_source_joint μ η obs fallback index hi hindex] at hgraph
  have hf : Measurable (fun z : (A × (B → A)) × S =>
      (index (z.1.1, z.2), z.1.2 (index (z.1.1, z.2)))) :=
    (measurable_of_countable (fun z : B × (B → A) => (z.1, z.2 z.1))).comp
      ((hi.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
        measurable_fst.snd)
  exact (ae_map_iff hf.aemeasurable (Set.to_countable _).measurableSet).1 hgraph

end MatroidProphet.Secretary

namespace MatroidProphet.Secretary

open MeasureTheory

abbrev SourceObservation (n : ℕ) := Bool × Finset (Fin n)

/-- The full source seed together with every conditional draw, all predrawn. -/
abbrev CouplingSeed (n : ℕ) :=
  Seed (mainSeedBits n) × (SourceObservation n → Seed (mainSeedBits n))

noncomputable def couplingObservation {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (r : Seed (mainSeedBits n)) : SourceObservation n :=
  (mainBranch r, (completeHiddenRule M hE).mask r)

noncomputable def couplingKernel {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (b : SourceObservation n) : Measure (Seed (mainSeedBits n)) :=
  conditionalSourceLaw (sourceSeedLaw n) (couplingObservation M hE) (fun _ => false) b

instance couplingKernel_probability {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (b : SourceObservation n) :
    IsProbabilityMeasure (couplingKernel M hE b) := by
  unfold couplingKernel
  infer_instance

/-- This initial seed law depends on the matroid but not on any weights. -/
noncomputable def couplingSeedLaw {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) : Measure (CouplingSeed n) :=
  (sourceSeedLaw n).prod (Measure.pi (couplingKernel M hE))

instance couplingSeedLaw_probability {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) : IsProbabilityMeasure (couplingSeedLaw M hE) := by
  unfold couplingSeedLaw
  infer_instance

/-- The cutoff is fixed before arrivals using only the first part of the seed. -/
noncomputable def couplingLength {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (q : CouplingSeed n) : Fin (n + 1) :=
  ⟨((completeHiddenRule M hE).mask q.1).card, by
    have h := Finset.card_le_univ ((completeHiddenRule M hE).mask q.1)
    simpa only [Fintype.card_fin, Nat.lt_succ_iff] using h⟩

/-- Lookup needs only the seed and the observed label set, not its weights or
the future suffix order. -/
def couplingDecode {n : ℕ} (q : CouplingSeed n) (P : Finset (Fin n)) :
    Seed (mainSeedBits n) := q.2 (mainBranch q.1, P)

noncomputable def couplingIndex {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (x : Seed (mainSeedBits n) × ArrivalOrder n) :
    SourceObservation n :=
  (mainBranch x.1, orderPrefix x.2 ((completeHiddenRule M hE).mask x.1).card)

/-- The remaining input is the independently proved random-prefix law, not a
hypothesis of the final secretary endpoint. -/
theorem coupling_joint_of_prefix_law {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ)
    (hprefix : ((sourceSeedLaw n).prod (uniformArrivalLaw n)).map (couplingIndex M hE) =
      (sourceSeedLaw n).map (couplingObservation M hE)) :
    ((couplingSeedLaw M hE).prod (uniformArrivalLaw n)).map
      (fun z : CouplingSeed n × ArrivalOrder n =>
        ((mainBranch z.1.1, orderPrefix z.2 (couplingLength M hE z.1).val),
          couplingDecode z.1 (orderPrefix z.2 (couplingLength M hE z.1).val))) =
      (sourceSeedLaw n).map (fun r => (couplingObservation M hE r, r)) := by
  exact precommitted_source_joint (sourceSeedLaw n) (uniformArrivalLaw n)
    (couplingObservation M hE) (fun _ => false) (couplingIndex M hE)
    (measurable_of_countable _) hprefix

theorem coupling_marginal_of_prefix_law {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ)
    (hprefix : ((sourceSeedLaw n).prod (uniformArrivalLaw n)).map (couplingIndex M hE) =
      (sourceSeedLaw n).map (couplingObservation M hE)) :
    ((couplingSeedLaw M hE).prod (uniformArrivalLaw n)).map
      (fun z : CouplingSeed n × ArrivalOrder n =>
        couplingDecode z.1 (orderPrefix z.2 (couplingLength M hE z.1).val)) =
      sourceSeedLaw n := by
  exact precommitted_source_marginal (sourceSeedLaw n) (uniformArrivalLaw n)
    (couplingObservation M hE) (fun _ => false) (couplingIndex M hE)
    (measurable_of_countable _) hprefix

theorem coupling_mask_ae_of_prefix_law {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ)
    (hprefix : ((sourceSeedLaw n).prod (uniformArrivalLaw n)).map (couplingIndex M hE) =
      (sourceSeedLaw n).map (couplingObservation M hE)) :
    ∀ᵐ z : CouplingSeed n × ArrivalOrder n
      ∂(couplingSeedLaw M hE).prod (uniformArrivalLaw n),
      (completeHiddenRule M hE).mask
          (couplingDecode z.1 (orderPrefix z.2 (couplingLength M hE z.1).val)) =
        orderPrefix z.2 (couplingLength M hE z.1).val := by
  filter_upwards [ae_precommitted_source_observation (sourceSeedLaw n) (uniformArrivalLaw n)
    (couplingObservation M hE) (fun _ => false) (couplingIndex M hE)
    (measurable_of_countable _) hprefix] with z hz
  exact congrArg Prod.snd hz

end MatroidProphet.Secretary

namespace MatroidProphet.Secretary

open MeasureTheory

/-- Concrete random-prefix identity, with no transport premise. -/
theorem coupling_source_prefix_law {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) :
    ((sourceSeedLaw n).prod (uniformArrivalLaw n)).map (couplingIndex M hE) =
      (sourceSeedLaw n).map (couplingObservation M hE) := by
  exact source_random_prefix_joint_law M hE

/-- The complete initial finite seed and independent arrival order reconstruct
exactly the original full source graph law. No assumption is added to an endpoint. -/
theorem coupling_joint_law {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) :
    ((couplingSeedLaw M hE).prod (uniformArrivalLaw n)).map
      (fun z : CouplingSeed n × ArrivalOrder n =>
        ((mainBranch z.1.1, orderPrefix z.2 (couplingLength M hE z.1).val),
          couplingDecode z.1 (orderPrefix z.2 (couplingLength M hE z.1).val))) =
      (sourceSeedLaw n).map (fun r => (couplingObservation M hE r, r)) :=
  coupling_joint_of_prefix_law M hE (coupling_source_prefix_law M hE)

/-- The decoded seed retains the law of every source bit, including unused bits. -/
theorem coupling_source_law {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) :
    ((couplingSeedLaw M hE).prod (uniformArrivalLaw n)).map
      (fun z : CouplingSeed n × ArrivalOrder n =>
        couplingDecode z.1 (orderPrefix z.2 (couplingLength M hE z.1).val)) =
      sourceSeedLaw n :=
  coupling_marginal_of_prefix_law M hE (coupling_source_prefix_law M hE)

/-- Almost-sure mask agreement for the concrete initial-seed experiment.
Every-seed feasibility separately uses the replay's mismatch-rejection guard. -/
theorem coupling_mask_ae {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) :
    ∀ᵐ z : CouplingSeed n × ArrivalOrder n
      ∂(couplingSeedLaw M hE).prod (uniformArrivalLaw n),
      (completeHiddenRule M hE).mask
          (couplingDecode z.1 (orderPrefix z.2 (couplingLength M hE z.1).val)) =
        orderPrefix z.2 (couplingLength M hE z.1).val :=
  coupling_mask_ae_of_prefix_law M hE (coupling_source_prefix_law M hE)

end MatroidProphet.Secretary

end OAI
