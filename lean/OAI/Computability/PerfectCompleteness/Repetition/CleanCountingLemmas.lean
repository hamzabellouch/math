import OAI.Computability.PerfectCompleteness.Construction.FactoredFunctionsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalKeys
import OAI.Computability.PerfectCompleteness.Foundations.ClauseSupportLemmas
import OAI.Computability.PerfectCompleteness.Foundations.QuotientTableAgreementLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanConditioning

namespace OAI


namespace PerfectCompleteness.CleanCounting

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning

noncomputable section

theorem expectation_event_factor {A : Type*} [Fintype A]
    (μ : FiniteDistribution A) (event : A → Bool) (a : ℝ) :
    μ.expectation (fun x => if event x then a else 1) =
      1 - (1 - a) * μ.probability event := by
  have hpoint (x : A) : μ.weight x * (if event x then a else 1) =
      μ.weight x - (1 - a) * (if event x then μ.weight x else 0) := by
    cases event x <;> simp
    ring
  change (∑ x, μ.weight x * (if event x then a else 1)) = _
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, μ.normalized]
  rfl

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def cleanCount (clean : (i : I) → Ω i → Bool) (x : (i : I) → Ω i) : Nat :=
  (Finset.univ.filter fun i => clean i (x i) = true).card

omit [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem power_cleanCount (clean : (i : I) → Ω i → Bool)
    (x : (i : I) → Ω i) (a : ℝ) :
    a ^ cleanCount clean x = ∏ i, if clean i (x i) = true then a else 1 := by
  rw [← Finset.prod_filter]
  simp [cleanCount]

theorem cleanCount_moment (P : (i : I) → FiniteDistribution (Ω i))
    (clean : (i : I) → Ω i → Bool) (a : ℝ) :
    (law P).expectation (fun x => a ^ cleanCount clean x) =
      ∏ i : I, (1 - (1 - a) * (P i).probability (clean i)) := by
  calc
    _ = (law P).expectation (fun x => ∏ i : I, if clean i (x i) then a else 1) :=
      FiniteDistribution.expectation_congr _
        (fun x => power_cleanCount (I := I) (Ω := Ω) clean x a)
    _ = ∏ i : I, (P i).expectation (fun x => if clean i x then a else 1) :=
      expectation_product (I := I) (Ω := Ω) P
        (fun (i : I) (x : Ω i) => if clean i x then a else 1)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact expectation_event_factor (P i) (clean i) a

theorem cleanCount_moment_le (P : (i : I) → FiniteDistribution (Ω i))
    (clean : (i : I) → Ω i → Bool) (a p₀ : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ 1)
    (lower : ∀ i, p₀ ≤ (P i).probability (clean i)) :
    (law P).expectation (fun x => a ^ cleanCount clean x) ≤
      (1 - (1 - a) * p₀) ^ Fintype.card I := by
  rw [cleanCount_moment]
  calc
    _ ≤ ∏ _i : I, (1 - (1 - a) * p₀) := by
      apply Finset.prod_le_prod₀
      · intro i _
        have h := mul_le_mul_of_nonneg_left ((P i).probability_le_one (clean i))
          (sub_nonneg.mpr ha')
        nlinarith
      · intro i _
        have h := mul_le_mul_of_nonneg_left (lower i) (sub_nonneg.mpr ha')
        linarith
    _ = _ := by simp


variable {E R T : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (T i)]

omit [Fintype I] [DecidableEq I] in
theorem kernel_clean_probability
    (μ : (i : I) → FiniteDistribution (E i))
    (ν : (i : I) → FiniteDistribution (R i))
    (kernel : (i : I) → E i → R i → FiniteDistribution (T i))
    (clean : (i : I) → E i → R i → T i → Bool) (p : I → ℝ)
    (constant : ∀ i e r, (kernel i e r).probability (clean i e r) = p i) (i : I) :
    (kernelJoint (μ i) (fun e => kernelJoint (ν i) (kernel i e))).probability
      (fun x => clean i x.1 x.2.1 x.2.2) = p i := by
  apply probability_kernelJoint_constant (μ i) _ _ (p i)
  intro e
  apply probability_kernelJoint_constant (ν i) _ _ (p i)
  intro r
  exact constant i e r

theorem kernel_cleanCount_moment
    (μ : (i : I) → FiniteDistribution (E i))
    (ν : (i : I) → FiniteDistribution (R i))
    (kernel : (i : I) → E i → R i → FiniteDistribution (T i))
    (clean : (i : I) → E i → R i → T i → Bool) (p : I → ℝ)
    (constant : ∀ i e r, (kernel i e r).probability (clean i e r) = p i) (a : ℝ) :
    (law (fun i => kernelJoint (μ i) (fun e => kernelJoint (ν i) (kernel i e)))).expectation
      (fun x => a ^ cleanCount (I := I) (Ω := fun i => E i × (R i × T i))
        (fun i y => clean i y.1 y.2.1 y.2.2) x) =
        ∏ i : I, (1 - (1 - a) * p i) := by
  rw [cleanCount_moment]
  simp only [kernel_clean_probability μ ν kernel clean p constant]


end
end PerfectCompleteness.CleanCounting


section

namespace PerfectCompleteness.MixedSupport

open ClauseSupport

variable {C Y : Type*}

theorem localKey_unused (s : Slot) (f : C → s.Domain → Y) (unused : Unused f) :
    localKey s f = .dropped := by
  classical
  cases s with
  | clause occurrence variableIDs signs =>
      change clauseKey occurrence variableIDs f = .dropped
      simp only [clauseKey, clauseMode_unused f unused]
  | bit variableID =>
      change (if Unused f then SlotKey.dropped else SlotKey.bit variableID) = SlotKey.dropped
      exact ite_eq_left unused

theorem localReduction_unused (s : Slot) (f : C → s.Domain → Y)
    (unused : Unused f) (u : s.Domain) : localReduction s f u = .dropped := by
  classical
  cases s with
  | clause occurrence variableIDs signs =>
      change clauseReduction f u = .dropped
      simp only [clauseReduction, clauseMode_unused f unused, reduceByMode]
  | bit variableID =>
      change (if Unused f then ReducedValue.dropped else ReducedValue.bit u) = ReducedValue.dropped
      exact ite_eq_left unused

end PerfectCompleteness.MixedSupport

namespace PerfectCompleteness.CleanKeyErasure

open ClauseSupport MixedSupport FactoredFunctions

variable {I Y : Type*} [DecidableEq I]

abbrev Retained (slots : I → Slot) (keep : I → Prop) :=
  (i : {i : I // keep i}) → (slots i.val).Domain

def retain (slots : I → Slot) (keep : I → Prop) :
    Assignment slots → Retained slots keep := fun x i => x i.val

theorem retain_update_of_not_kept (slots : I → Slot) (keep : I → Prop)
    (x : Assignment slots) (i : I) (not_kept : ¬ keep i) (u : (slots i).Domain) :
    retain slots keep (Function.update x i u) = retain slots keep x := by
  funext j
  have hji : j.val ≠ i := by
    intro h
    exact not_kept (h ▸ j.property)
  simp only [retain, Function.update_of_ne hji]

theorem section_unused_of_retained (slots : I → Slot) (keep : I → Prop)
    (f : Assignment slots → Y)
    (constant : ∀ x y, retain slots keep x = retain slots keep y → f x = f y)
    (i : I) (not_kept : ¬ keep i) : Unused (sectionFunction slots f i) := by
  intro context u v
  apply constant
  exact (retain_update_of_not_kept slots keep context i not_kept u).trans
    (retain_update_of_not_kept slots keep context i not_kept v).symm

theorem section_unused_of_factor (slots : I → Slot) (keep : I → Prop)
    (f : Retained slots keep → Y) (i : I) (not_kept : ¬ keep i) :
    Unused (sectionFunction slots (f ∘ retain slots keep) i) := by
  apply section_unused_of_retained slots keep (f ∘ retain slots keep)
    (fun x y h => congrArg f h) i not_kept

theorem keyFields_dropped_of_retained (slots : I → Slot) (keep : I → Prop)
    (f : Assignment slots → Y)
    (constant : ∀ x y, retain slots keep x = retain slots keep y → f x = f y)
    (i : I) (not_kept : ¬ keep i) : keyFields slots f i = .dropped :=
  localKey_unused (slots i) (sectionFunction slots f i)
    (section_unused_of_retained slots keep f constant i not_kept)

theorem reduction_dropped_of_retained (slots : I → Slot) (keep : I → Prop)
    (f : Assignment slots → Y)
    (constant : ∀ x y, retain slots keep x = retain slots keep y → f x = f y)
    (i : I) (not_kept : ¬ keep i) (x : Assignment slots) :
    reduction slots f x i = .dropped :=
  localReduction_unused (slots i) (sectionFunction slots f i)
    (section_unused_of_retained slots keep f constant i not_kept) (x i)

section Scalar

variable {𝕜 : Type*} [Field 𝕜]

theorem section_unused_of_factoring (slots : I → Slot) (keep : I → Prop)
    (f : Assignment slots → 𝕜) (factors : f ∈ factoringSpace (retain slots keep))
    (i : I) (not_kept : ¬ keep i) : Unused (sectionFunction slots f i) :=
  section_unused_of_retained slots keep f factors i not_kept

theorem keyFields_dropped_of_factoring (slots : I → Slot) (keep : I → Prop)
    (f : Assignment slots → 𝕜) (factors : f ∈ factoringSpace (retain slots keep))
    (i : I) (not_kept : ¬ keep i) : keyFields slots f i = .dropped :=
  keyFields_dropped_of_retained slots keep f factors i not_kept

theorem reduction_dropped_of_factoring (slots : I → Slot) (keep : I → Prop)
    (f : Assignment slots → 𝕜) (factors : f ∈ factoringSpace (retain slots keep))
    (i : I) (not_kept : ¬ keep i) (x : Assignment slots) :
    reduction slots f x i = .dropped :=
  reduction_dropped_of_retained slots keep f factors i not_kept x

end Scalar


variable {n : Nat}

theorem retainedKeys_only_kept (slots : Fin n → Slot) (keep : Fin n → Prop)
    (f : Assignment slots → Y)
    (constant : ∀ x y, retain slots keep x = retain slots keep y → f x = f y)
    (entry : Fin n × SlotKey) (present : entry ∈ retainedKeys slots f) : keep entry.1 := by
  classical
  unfold retainedKeys at present
  obtain ⟨in_map, not_dropped⟩ := List.mem_filter.mp present
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp in_map
  by_contra not_kept
  exact (of_decide_eq_true not_dropped)
    (keyFields_dropped_of_retained slots keep f constant i not_kept)

theorem not_mem_retainedKeys_of_not_kept (slots : Fin n → Slot) (keep : Fin n → Prop)
    (f : Assignment slots → Y)
    (constant : ∀ x y, retain slots keep x = retain slots keep y → f x = f y)
    (i : Fin n) (not_kept : ¬ keep i) (metadata : SlotKey) :
    (i, metadata) ∉ retainedKeys slots f := by
  intro present
  exact not_kept (retainedKeys_only_kept slots keep f constant (i, metadata) present)

theorem keyFields_const (slots : Fin n → Slot) (value : Y) (i : Fin n) :
    keyFields slots (fun _ => value) i = .dropped :=
  localKey_unused (slots i) (sectionFunction slots (fun _ => value) i)
    (fun _ _ _ => rfl)

theorem retainedKeys_const (slots : Fin n → Slot) (value : Y) :
    retainedKeys slots (fun _ => value) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry present
  exact retainedKeys_only_kept slots (fun _ => False) (fun _ => value)
    (fun _ _ _ => rfl) entry present

end PerfectCompleteness.CleanKeyErasure

end


namespace PerfectCompleteness.CleanKeyFactorization

open ClauseSupport MixedSupport CanonicalKeys CleanKeyErasure
open scoped Classical

noncomputable section

variable {I Y : Type*} [DecidableEq I]

abbrev retainedSlots (slots : I → Slot) (keep : I → Prop) : {i : I // keep i} → Slot :=
  fun i => slots i.val

def fill (slots : I → Slot) (keep : I → Prop)
    (x : Assignment (retainedSlots slots keep)) : Assignment slots :=
  fun i => if h : keep i then x ⟨i, h⟩ else Classical.choice (inferInstance : Nonempty (slots i).Domain)

omit [DecidableEq I] in
theorem retain_fill (slots : I → Slot) (keep : I → Prop)
    (x : Assignment (retainedSlots slots keep)) : retain slots keep (fill slots keep x) = x := by
  funext i
  simp only [retain, fill, dite_eq_left i.property]

omit [DecidableEq I] in
theorem retain_surjective (slots : I → Slot) (keep : I → Prop) :
    Function.Surjective (retain slots keep) :=
  fun x => ⟨fill slots keep x, retain_fill slots keep x⟩

theorem retain_update (slots : I → Slot) (keep : I → Prop)
    (x : Assignment slots) (i : {i : I // keep i}) (u : (slots i.val).Domain) :
    retain slots keep (Function.update x i.val u) =
      Function.update (retain slots keep x) i u :=
  Function.update_comp_eq_of_injective' x Subtype.val_injective i u

theorem sectionFunction_factor (slots : I → Slot) (keep : I → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) (i : {i : I // keep i}) :
    sectionFunction slots (g ∘ retain slots keep) i.val =
      pull (sectionFunction (retainedSlots slots keep) g i) (retain slots keep) id := by
  funext context u
  change g (retain slots keep (Function.update context i.val u)) =
    g (Function.update (retain slots keep context) i u)
  rw [retain_update]

theorem keyFields_kept (slots : I → Slot) (keep : I → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) (i : {i : I // keep i}) :
    keyFields slots (g ∘ retain slots keep) i.val =
      keyFields (retainedSlots slots keep) g i := by
  change localKey (slots i.val) (sectionFunction slots (g ∘ retain slots keep) i.val) = _
  rw [sectionFunction_factor]
  exact localKey_projection (Projection.keep (slots i.val))
    (sectionFunction (retainedSlots slots keep) g i)
    (retain slots keep) (retain_surjective slots keep)

theorem reduction_kept (slots : I → Slot) (keep : I → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) (i : {i : I // keep i})
    (x : Assignment slots) :
    reduction slots (g ∘ retain slots keep) x i.val =
      reduction (retainedSlots slots keep) g (retain slots keep x) i := by
  change localReduction (slots i.val)
    (sectionFunction slots (g ∘ retain slots keep) i.val) (x i.val) = _
  rw [sectionFunction_factor]
  exact localReduction_projection (Projection.keep (slots i.val))
    (sectionFunction (retainedSlots slots keep) g i)
    (retain slots keep) (retain_surjective slots keep) (x i.val)

def embeddedFields (keep : I → Prop) (slots : {i : I // keep i} → Slot)
    (g : Assignment slots → Y) (i : I) : SlotKey :=
  if h : keep i then keyFields slots g ⟨i, h⟩ else .dropped

def embeddedReduction (keep : I → Prop) (slots : {i : I // keep i} → Slot)
    (g : Assignment slots → Y) (x : Assignment slots) (i : I) : ReducedValue :=
  if h : keep i then reduction slots g x ⟨i, h⟩ else .dropped

theorem keyFields_factor (slots : I → Slot) (keep : I → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) :
    keyFields slots (g ∘ retain slots keep) = embeddedFields keep (retainedSlots slots keep) g := by
  funext i
  by_cases hi : keep i
  · simpa only [embeddedFields, dite_eq_left hi] using keyFields_kept slots keep g ⟨i, hi⟩
  · rw [embeddedFields, dite_eq_right hi]
    exact keyFields_dropped_of_retained slots keep (g ∘ retain slots keep)
      (fun x y h => congrArg g h) i hi

theorem reduction_factor (slots : I → Slot) (keep : I → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) (x : Assignment slots) :
    reduction slots (g ∘ retain slots keep) x =
      embeddedReduction keep (retainedSlots slots keep) g (retain slots keep x) := by
  funext i
  by_cases hi : keep i
  · simpa only [embeddedReduction, dite_eq_left hi] using reduction_kept slots keep g ⟨i, hi⟩ x
  · rw [embeddedReduction, dite_eq_right hi]
    exact reduction_dropped_of_retained slots keep (g ∘ retain slots keep)
      (fun x y h => congrArg g h) i hi x

theorem embeddedReduction_constant [Finite I]
    (keep : I → Prop) (slots : {i : I // keep i} → Slot) (g : Assignment slots → Y) :
    ReducedPartition.ConstantOnFibers (embeddedReduction keep slots g) g := by
  intro x y h
  apply constant_on_reduction_fibers slots g
  funext i
  have hi := congrFun h i.val
  simpa only [embeddedReduction, dite_eq_left i.property] using hi


variable {n : Nat}

def retainedMetadata (keep : Fin n → Prop) (slots : {i : Fin n // keep i} → Slot)
    (g : Assignment slots → Y) : List (Fin n × SlotKey) :=
  ((List.finRange n).map (fun i => (i, embeddedFields keep slots g i))).filter
    (fun entry => decide (entry.2 ≠ .dropped))

def retainedKey (side : Side) (keep : Fin n → Prop)
    (slots : {i : Fin n // keep i} → Slot) (g : Assignment slots → Y) : Key n where
  side := side
  retained := retainedMetadata keep slots g
  partition := ReducedPartition.parts (embeddedReduction keep slots g) g

theorem retainedKeys_factor (slots : Fin n → Slot) (keep : Fin n → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) :
    retainedKeys slots (g ∘ retain slots keep) =
      retainedMetadata keep (retainedSlots slots keep) g := by
  simp only [retainedKeys, retainedMetadata, keyFields_factor]

theorem partition_factor (slots : Fin n → Slot) (keep : Fin n → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) :
    CanonicalKeys.partition slots (g ∘ retain slots keep) =
      ReducedPartition.parts (embeddedReduction keep (retainedSlots slots keep) g) g :=
  ReducedPartition.parts_eq_of_pullback (retain slots keep) (retain_surjective slots keep)
    (reduction slots (g ∘ retain slots keep))
    (embeddedReduction keep (retainedSlots slots keep) g)
    (g ∘ retain slots keep) g (reduction_factor slots keep g) (fun _ => rfl)

theorem key_factor (side : Side) (slots : Fin n → Slot) (keep : Fin n → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) :
    key side slots (g ∘ retain slots keep) =
      retainedKey side keep (retainedSlots slots keep) g := by
  simp only [key, retainedKey, retainedKeys_factor, partition_factor]

theorem retainedKey_nonempty (side : Side) (keep : Fin n → Prop)
    (slots : {i : Fin n // keep i} → Slot) (g : Assignment slots → Y) :
    (retainedKey side keep slots g).partition.Nonempty := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (Assignment slots))
  exact ⟨ReducedPartition.fiber (embeddedReduction keep slots g) g x, ⟨x, rfl⟩⟩

def retainedQueryKey (side : Side) (keep : Fin n → Prop)
    (slots : {i : Fin n // keep i} → Slot) (g : Assignment slots → Y) :
    KeyStrategy.NonemptyKey n :=
  ⟨retainedKey side keep slots g, retainedKey_nonempty side keep slots g⟩

theorem queryKey_factor (side : Side) (slots : Fin n → Slot) (keep : Fin n → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) :
    KeyStrategy.queryKey side slots (g ∘ retain slots keep) =
      retainedQueryKey side keep (retainedSlots slots keep) g := by
  apply Subtype.ext
  exact key_factor side slots keep g

theorem label_factor (labeling : KeyStrategy.Strategy n) (side : Side)
    (slots : Fin n → Slot) (keep : Fin n → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) :
    (KeyStrategy.label labeling side slots (g ∘ retain slots keep)).val =
      (labeling (retainedQueryKey side keep (retainedSlots slots keep) g)).val :=
  congrArg (fun k : KeyStrategy.NonemptyKey n => (labeling k).val)
    (queryKey_factor side slots keep g)

def retainedResponse (labeling : KeyStrategy.Strategy n) (side : Side)
    (keep : Fin n → Prop) (slots : {i : Fin n // keep i} → Slot)
    (g : Assignment slots → Y) : Y :=
  ReducedPartition.output (embeddedReduction keep slots g) g
    (labeling (retainedQueryKey side keep slots g))

theorem response_factor (labeling : KeyStrategy.Strategy n) (side : Side)
    (slots : Fin n → Slot) (keep : Fin n → Prop)
    (g : Assignment (retainedSlots slots keep) → Y) :
    KeyStrategy.response labeling side slots (g ∘ retain slots keep) =
      retainedResponse labeling side keep (retainedSlots slots keep) g :=
  ReducedPartition.output_eq_of_shared_part (retain slots keep)
    (reduction slots (g ∘ retain slots keep))
    (embeddedReduction keep (retainedSlots slots keep) g)
    (g ∘ retain slots keep) g (reduction_factor slots keep g) (fun _ => rfl)
    (embeddedReduction_constant keep (retainedSlots slots keep) g)
    (KeyStrategy.label labeling side slots (g ∘ retain slots keep))
    (labeling (retainedQueryKey side keep (retainedSlots slots keep) g))
    (label_factor labeling side slots keep g)


end
end PerfectCompleteness.CleanKeyFactorization

end OAI
