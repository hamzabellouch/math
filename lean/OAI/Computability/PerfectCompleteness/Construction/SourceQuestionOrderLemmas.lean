import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.FinRange
import OAI.Computability.PerfectCompleteness.Construction.HiddenChildMixture
import OAI.Computability.PerfectCompleteness.Construction.TreeCanonical
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalArrays
import OAI.Computability.PerfectCompleteness.Foundations.KeyFiniteness
import OAI.Computability.PerfectCompleteness.Machines.TupleIndexMachine
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas
import OAI.Computability.PerfectCompleteness.Sampling.PreliminarySampler
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.UniformDensity
import OAI.Computability.UniqueGames.Foundations.MixtureLemmas

namespace OAI


namespace PerfectCompleteness.SourceQuestionOrder

open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t m : Nat}

def questionToTuple (question : PreliminarySampler.Questions branch n t m) :
    Fin (TreeCanonical.locationCount branch n t) → Fin m :=
  fun j => question ((TreeCanonical.numbering branch n t).symm j).1
    ((TreeCanonical.numbering branch n t).symm j).2

def tupleToQuestion (tuple : Fin (TreeCanonical.locationCount branch n t) → Fin m) :
    PreliminarySampler.Questions branch n t m :=
  fun leaf coordinate => tuple (TreeCanonical.numbering branch n t (leaf, coordinate))

@[simp] theorem tupleToQuestion_questionToTuple
    (question : PreliminarySampler.Questions branch n t m) :
    tupleToQuestion (questionToTuple question) = question := by
  funext leaf coordinate
  simp only [tupleToQuestion, questionToTuple, Equiv.symm_apply_apply]

@[simp] theorem questionToTuple_tupleToQuestion
    (tuple : Fin (TreeCanonical.locationCount branch n t) → Fin m) :
    questionToTuple (tupleToQuestion (branch := branch) (n := n) (t := t) tuple) = tuple := by
  funext j
  simp only [questionToTuple, tupleToQuestion, Prod.mk.eta, Equiv.apply_symm_apply]

def questionTupleEquiv (branch : Nat → Nat) (n t m : Nat) :
    PreliminarySampler.Questions branch n t m ≃
      (Fin (TreeCanonical.locationCount branch n t) → Fin m) where
  toFun := questionToTuple
  invFun := tupleToQuestion
  left_inv := tupleToQuestion_questionToTuple
  right_inv := questionToTuple_tupleToQuestion

def sourceOrder (branch : Nat → Nat) (n t m : Nat) :
    List (PreliminarySampler.Questions branch n t m) :=
  (MachineTupleOdometer.tupleOrder m (TreeCanonical.locationCount branch n t)).reverse.map
    tupleToQuestion

@[simp] theorem sourceOrder_length (branch : Nat → Nat) (n t m : Nat) :
    (sourceOrder branch n t m).length = m ^ TreeCanonical.locationCount branch n t := by
  simp only [sourceOrder, List.length_map, List.length_reverse,
    MachineTupleOdometer.tupleOrder_length]

theorem sourceOrder_nodup (branch : Nat → Nat) (n t m : Nat) :
    (sourceOrder branch n t m).Nodup := by
  apply List.Nodup.map (questionTupleEquiv branch n t m).symm.injective
  apply List.nodup_reverse.mpr
  exact List.nodup_ofFn.mpr
    (finFunctionFinEquiv (m := m) (n := TreeCanonical.locationCount branch n t)).symm.injective

theorem mem_sourceOrder (question : PreliminarySampler.Questions branch n t m) :
    question ∈ sourceOrder branch n t m := by
  apply List.mem_map.mpr
  refine ⟨questionToTuple question, ?_, tupleToQuestion_questionToTuple question⟩
  rw [List.mem_reverse]
  change questionToTuple question ∈ List.ofFn
    (finFunctionFinEquiv (m := m) (n := TreeCanonical.locationCount branch n t)).symm
  apply List.mem_ofFn.mpr
  exact ⟨finFunctionFinEquiv (questionToTuple question), Equiv.symm_apply_apply _ _⟩

@[simp] theorem sourceOrder_toFinset (branch : Nat → Nat) (n t m : Nat) :
    (sourceOrder branch n t m).toFinset = Finset.univ := by
  ext question
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact mem_sourceOrder question

theorem sum_map_sourceOrder {A : Type*} [AddCommMonoid A]
    (f : PreliminarySampler.Questions branch n t m → A) :
    ((sourceOrder branch n t m).map f).sum = ∑ question, f question := by
  rw [← List.sum_toFinset f (sourceOrder_nodup branch n t m), sourceOrder_toFinset]

def numberedClauseIDs (question : PreliminarySampler.Questions branch n t m) : List Nat :=
  List.ofFn (fun j => (questionToTuple question j).val)

@[simp] theorem numberedClauseIDs_length
    (question : PreliminarySampler.Questions branch n t m) :
    (numberedClauseIDs question).length = TreeCanonical.locationCount branch n t := by
  simp only [numberedClauseIDs, List.length_ofFn]

@[simp] theorem numberedClauseIDs_tupleToQuestion
    (tuple : Fin (TreeCanonical.locationCount branch n t) → Fin m) :
    numberedClauseIDs (tupleToQuestion (branch := branch) (n := n) (t := t) tuple) =
      List.ofFn (fun j => (tuple j).val) := by
  simp only [numberedClauseIDs, questionToTuple_tupleToQuestion]

theorem outputBlock_all_eq_sourceOrder (branch : Nat → Nat) (n t m : Nat) :
    TupleEnumerationMachine.outputBlock (width := TreeCanonical.locationCount branch n t)
        m (TreeCanonical.locationCount branch n t)
        (fun _ => 0) =
      (sourceOrder branch n t m).flatMap (fun question => encodeWords (numberedClauseIDs question)) := by
  rw [TupleEnumerationMachine.outputBlock_all]
  simp only [sourceOrder, List.flatMap_map,
    numberedClauseIDs_tupleToQuestion]

theorem output_eq_sourceOrder (branch : Nat → Nat) (n t m : Nat) :
    TupleIndexMachine.output (TreeCanonical.locationCount branch n t) m =
      (sourceOrder branch n t m).flatMap (fun question => encodeWords (numberedClauseIDs question)) := by
  exact outputBlock_all_eq_sourceOrder branch n t m

def sourceOutputsInTime (branch : Nat → Nat) (n t m : Nat) (positive : 0 < m) :
    TM2OutputsInTime (TupleIndexMachine.machine (TreeCanonical.locationCount branch n t))
      (encodeWord m)
      (some ((sourceOrder branch n t m).flatMap
        (fun question => encodeWords (numberedClauseIDs question))))
      (TupleIndexMachine.totalBudget (TreeCanonical.locationCount branch n t) m) := by
  exact Eq.mp
    (congrArg (fun words : List Bool =>
      TM2OutputsInTime (TupleIndexMachine.machine (TreeCanonical.locationCount branch n t))
        (encodeWord m) (some words)
        (TupleIndexMachine.totalBudget (TreeCanonical.locationCount branch n t) m))
      (output_eq_sourceOrder branch n t m))
    (TupleIndexMachine.outputsInTime (width := TreeCanonical.locationCount branch n t) m positive)

end

end PerfectCompleteness.SourceQuestionOrder


namespace PerfectCompleteness.TreeCardinality

open TreeSourceSpaces HierarchicalArrays
open scoped BigOperators

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

def domainBound (branch : Nat → Nat) (n t : Nat) : Nat :=
  (7 ^ t) ^ Fintype.card (RecursiveSpaces.Slots branch n)

def functionBound (branch : Nat → Nat) (n t : Nat) : Nat :=
  2 ^ domainBound branch n t

theorem domain_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (Domain slots) ≤ domainBound branch n t := by
  change Nat.card (∀ leaf, LeafDomain slots leaf) ≤ _
  rw [Nat.card_pi]
  calc
    _ ≤ ∏ _leaf : RecursiveSpaces.Slots branch n, (7 ^ t : Nat) :=
      Finset.prod_le_prod (fun leaf _ =>
        CanonicalKeys.card_assignment_le_seven_pow (slots leaf))
    _ = domainBound branch n t := by simp [domainBound]

theorem subspace_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (V : Submodule F2 (Domain slots → F2)) :
    Nat.card V ≤ functionBound branch n t := by
  calc
    Nat.card V ≤ Nat.card (Domain slots → F2) :=
      Nat.card_le_card_of_injective (fun f : V => f.val) Subtype.val_injective
    _ = 2 ^ Nat.card (Domain slots) := by rw [Nat.card_fun, Nat.card_zmod]
    _ ≤ functionBound branch n t :=
      pow_le_pow_right₀ (by decide : (1 : Nat) ≤ 2) (domain_card_le slots)

theorem H_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (H slots) ≤ functionBound branch n t :=
  subspace_card_le slots (H slots)

theorem square_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (PointwiseSpaces.squareSpace (H slots)) ≤ functionBound branch n t :=
  subspace_card_le slots (PointwiseSpaces.squareSpace (H slots))

def arraysBound (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) : Nat :=
  ∏ node : Nodes branch n,
    functionBound branch (Nodes.height node) t ^ rows (Nodes.height node)

theorem arrays_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :
    Nat.card (Arrays slots rows) ≤ arraysBound branch n t rows := by
  change Nat.card (∀ node : Nodes branch n,
    Fin (rows (Nodes.height node)) → H (nodeSlots slots node)) ≤ _
  rw [Nat.card_pi]
  apply Finset.prod_le_prod
  intro node _
  rw [Nat.card_fun, Nat.card_fin]
  exact pow_le_pow_left₀ (Nat.zero_le _) (H_card_le (nodeSlots slots node)) _

theorem source_questions_card (m : Nat) :
    Nat.card (PreliminarySampler.Questions branch n t m) =
      m ^ (t * Fintype.card (RecursiveSpaces.Slots branch n)) := by
  simp only [PreliminarySampler.Questions, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_fin, ← pow_mul]

theorem source_base_card (m : Nat) :
    Nat.card (PreliminarySampler.Base branch n t m) =
      m ^ (t * Fintype.card (RecursiveSpaces.Slots branch n)) *
        Fintype.card (RecursiveSpaces.Slots branch n) := by
  rw [Nat.card_prod, source_questions_card, Nat.card_eq_fintype_card]

end
end PerfectCompleteness.TreeCardinality


namespace PerfectCompleteness.ChildBlockCardinality

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

abbrev Raw (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  (Fin calls → squareSpace (H slots)) × Arrays slots rows

instance rawFintype (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Raw calls rows slots) := Fintype.ofFinite _

instance rawNonempty (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Raw calls rows slots) := ⟨(fun _ => 0, fun _ _ => 0)⟩

def bound (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) : Nat :=
  TreeCardinality.functionBound branch n t ^ calls *
    TreeCardinality.arraysBound branch n t rows

theorem card_le (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (Raw calls rows slots) ≤ bound branch n t calls rows := by
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]
  exact Nat.mul_le_mul
    (pow_le_pow_left₀ (Nat.zero_le _) (TreeCardinality.square_card_le slots) calls)
    (TreeCardinality.arrays_card_le slots rows)

theorem fintype_card_le (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype.card (Raw calls rows slots) ≤ bound branch n t calls rows := by
  simpa only [Nat.card_eq_fintype_card] using card_le calls rows slots

theorem bound_pos (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    0 < bound branch n t calls rows :=
  lt_of_lt_of_le (Nat.card_pos (α := Raw calls rows slots)) (card_le calls rows slots)

def density {calls : Nat} {rows : Nat → Nat}
    {slots : Slots branch n → Fin t → MixedSupport.Slot}
    (μ : FiniteDistribution (Raw calls rows slots)) : Raw calls rows slots → ℝ :=
  UniformDensity.density μ

theorem weight_eq {calls : Nat} {rows : Nat → Nat}
    {slots : Slots branch n → Fin t → MixedSupport.Slot}
    (μ : FiniteDistribution (Raw calls rows slots)) (x : Raw calls rows slots) :
    μ.weight x = (FiniteDistribution.uniform (Raw calls rows slots)).weight x * density μ x :=
  UniformDensity.weight_eq μ x

theorem mean_one {calls : Nat} {rows : Nat → Nat}
    {slots : Slots branch n → Fin t → MixedSupport.Slot}
    (μ : FiniteDistribution (Raw calls rows slots)) :
    (FiniteDistribution.uniform (Raw calls rows slots)).expectation (density μ) = 1 :=
  UniformDensity.mean_one μ

theorem density_le {calls : Nat} {rows : Nat → Nat}
    {slots : Slots branch n → Fin t → MixedSupport.Slot}
    (μ : FiniteDistribution (Raw calls rows slots)) (x : Raw calls rows slots) :
    density μ x ≤ (bound branch n t calls rows : ℝ) :=
  (UniformDensity.density_le_card μ x).trans
    (by exact_mod_cast fintype_card_le calls rows slots)

theorem second_moment_le {calls : Nat} {rows : Nat → Nat}
    {slots : Slots branch n → Fin t → MixedSupport.Slot}
    (μ : FiniteDistribution (Raw calls rows slots)) :
    (FiniteDistribution.uniform (Raw calls rows slots)).expectation
      (fun x => (density μ x - 1) ^ 2) ≤ (bound branch n t calls rows : ℝ) ^ 2 := by
  apply UniformDensity.second_moment_le
  exact_mod_cast fintype_card_le calls rows slots

end
end PerfectCompleteness.ChildBlockCardinality


namespace PerfectCompleteness.ChildBlockMixture

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

section General

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]

def component (Q : (i : I) → FiniteDistribution (Ω i)) (chosen i : I) :
    FiniteDistribution (Ω i) :=
  if h : chosen = i then h ▸ Q chosen else FiniteDistribution.uniform (Ω i)

def reference : FiniteDistribution ((i : I) → Ω i) :=
  FiniteProduct.law (fun i => FiniteDistribution.uniform (Ω i))

def special (Q : (i : I) → FiniteDistribution (Ω i)) (chosen : I) :
    FiniteDistribution ((i : I) → Ω i) :=
  FiniteProduct.law (component Q chosen)

def mixture (Q : (i : I) → FiniteDistribution (Ω i)) :
    FiniteDistribution ((i : I) → Ω i) :=
  HiddenChildMixture.mixture (special Q)

omit [Fintype I] [Nonempty I] in
theorem component_weight (Q : (i : I) → FiniteDistribution (Ω i))
    (chosen i : I) (x : Ω i) :
    (component Q chosen i).weight x =
      (FiniteDistribution.uniform (Ω i)).weight x *
        FiniteProduct.factor chosen (UniformDensity.density (Q chosen)) i x := by
  by_cases h : i = chosen
  · subst i
    simp only [component, FiniteProduct.factor_self]
    exact UniformDensity.weight_eq (Q chosen) x
  · simp only [component, dite_eq_right (Ne.symm h),
      FiniteProduct.factor_other chosen i h, mul_one]

omit [Nonempty I] in
theorem special_weight (Q : (i : I) → FiniteDistribution (Ω i))
    (chosen : I) (x : (i : I) → Ω i) :
    (special Q chosen).weight x = (reference (Ω := Ω)).weight x *
      UniformDensity.density (Q chosen) (x chosen) := by
  change (∏ i, (component Q chosen i).weight (x i)) =
    (∏ i, (FiniteDistribution.uniform (Ω i)).weight (x i)) * _
  simp_rw [component_weight]
  rw [Finset.prod_mul_distrib, FiniteProduct.product_factor]

theorem observed_variation {Γ : Type*} [Fintype Γ]
    (Q : (i : I) → FiniteDistribution (Ω i)) (L : ℝ)
    (hcard : ∀ i, (Fintype.card (Ω i) : ℝ) ≤ L)
    (observe : ((i : I) → Ω i) → Γ) :
    ((mixture Q).pushforward observe).totalVariation
      ((reference (Ω := Ω)).pushforward observe) ≤
        Real.sqrt (L ^ 2 / Fintype.card I) / 2 := by
  apply HiddenChildMixture.observed_mixture_variation
    (fun i => FiniteDistribution.uniform (Ω i)) (special Q)
    (fun i => UniformDensity.density (Q i))
  · exact special_weight Q
  · intro i
    exact UniformDensity.mean_one (Q i)
  · intro i
    exact UniformDensity.second_moment_le (Q i) L (hcard i)

end General

theorem actual_observed_variation
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {branch : Nat → Nat} {n t : Nat} (calls : Nat) (rows : Nat → Nat)
    (slots : I → RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (Q : (i : I) → FiniteDistribution (ChildBlockCardinality.Raw calls rows (slots i)))
    {Γ : Type*} [Fintype Γ]
    (observe : ((i : I) → ChildBlockCardinality.Raw calls rows (slots i)) → Γ) :
    ((mixture Q).pushforward observe).totalVariation
      ((reference (Ω := fun i => ChildBlockCardinality.Raw calls rows (slots i))).pushforward
        observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 /
        Fintype.card I) / 2 := by
  apply observed_variation Q
  intro i
  exact_mod_cast ChildBlockCardinality.fintype_card_le calls rows (slots i)

end
end PerfectCompleteness.ChildBlockMixture


namespace PerfectCompleteness.ChildBlockMixture

open UniqueGamesTheorem.Foundations.Games

noncomputable section

theorem conditional_actual_observed_variation
    {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I] [Nonempty I]
    {branch : Nat → Nat} {n t : Nat} (calls : Nat) (rows : Nat → Nat)
    (slots : S → I → RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (μ : FiniteDistribution S)
    (Q : (s : S) → (i : I) →
      FiniteDistribution (ChildBlockCardinality.Raw calls rows (slots s i)))
    {Γ : Type*} [Fintype Γ]
    (observe : (Σ s : S, (i : I) → ChildBlockCardinality.Raw calls rows (slots s i)) → Γ) :
    ((CompletionSoundness.sigmaLaw μ (fun s => mixture (Q s))).pushforward observe).totalVariation
      ((CompletionSoundness.sigmaLaw μ
        (fun s => reference (Ω := fun i => ChildBlockCardinality.Raw calls rows (slots s i)))).pushforward observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 /
        Fintype.card I) / 2 := by
  refine ConditionalVariation.observed_sigma_le_const μ
    (fun s => mixture (Q s))
    (fun s => reference (Ω := fun i => ChildBlockCardinality.Raw calls rows (slots s i)))
    _ ?_ observe
  intro s
  simpa only [FiniteDistribution.pushforward_id] using
    actual_observed_variation calls rows (slots s) (Q s)
      (id : ((i : I) → ChildBlockCardinality.Raw calls rows (slots s i)) →
        ((i : I) → ChildBlockCardinality.Raw calls rows (slots s i)))

end
end PerfectCompleteness.ChildBlockMixture


namespace PerfectCompleteness.ChildBlockContinuation

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    {T : I → Type*} [∀ i, Fintype (T i)]

def continuedSpecial (Q : (i : I) → T i → FiniteDistribution (Ω i))
    (chosen : I) (t : T chosen) : FiniteDistribution ((i : I) → Ω i) :=
  ChildBlockMixture.special
    (Function.update (fun i => FiniteDistribution.uniform (Ω i)) chosen (Q chosen t))
    chosen

omit [Nonempty I] [∀ i, Fintype (T i)] in
theorem continuedSpecial_eq_product
    (Q : (i : I) → T i → FiniteDistribution (Ω i)) (chosen : I) (t : T chosen) :
    continuedSpecial Q chosen t = FiniteProduct.law
      (fun i => if h : chosen = i then h ▸ Q chosen t else
        FiniteDistribution.uniform (Ω i)) := by
  unfold continuedSpecial ChildBlockMixture.special
  apply congrArg (fun P : (i : I) → FiniteDistribution (Ω i) => FiniteProduct.law P)
  funext i
  by_cases h : chosen = i
  · subst i
    simp only [ChildBlockMixture.component, Function.update_self]
  · simp only [ChildBlockMixture.component, dite_eq_right h]

omit [Nonempty I] [∀ i, Fintype (T i)] in
theorem continuedSpecial_weight
    (Q : (i : I) → T i → FiniteDistribution (Ω i))
    (chosen : I) (t : T chosen) (x : (i : I) → Ω i) :
    (continuedSpecial Q chosen t).weight x =
      (ChildBlockMixture.reference (Ω := Ω)).weight x *
        UniformDensity.density (Q chosen t) (x chosen) := by
  unfold continuedSpecial
  rw [ChildBlockMixture.special_weight, Function.update_self]

omit [Nonempty I] in
theorem average_special (P : (i : I) → FiniteDistribution (T i))
    (Q : (i : I) → T i → FiniteDistribution (Ω i)) (chosen : I) :
    (P chosen).mixture (continuedSpecial Q chosen) =
      ChildBlockMixture.special (fun i => (P i).mixture (Q i)) chosen := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∑ t, (P chosen).weight t * (continuedSpecial Q chosen t).weight x) = _
  simp_rw [continuedSpecial_weight]
  rw [ChildBlockMixture.special_weight]
  change (∑ t, (P chosen).weight t *
      ((ChildBlockMixture.reference (Ω := Ω)).weight x *
        ((Fintype.card (Ω chosen) : ℝ) * (Q chosen t).weight (x chosen)))) =
    (ChildBlockMixture.reference (Ω := Ω)).weight x *
      ((Fintype.card (Ω chosen) : ℝ) *
        ∑ t, (P chosen).weight t * (Q chosen t).weight (x chosen))
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem hidden_average (P : (i : I) → FiniteDistribution (T i))
    (Q : (i : I) → T i → FiniteDistribution (Ω i)) :
    HiddenChildMixture.mixture (fun i => (P i).mixture (continuedSpecial Q i)) =
      ChildBlockMixture.mixture (fun i => (P i).mixture (Q i)) := by
  simp only [average_special, ChildBlockMixture.mixture]

theorem uniform_average (P : (i : I) → FiniteDistribution (T i))
    (Q : (i : I) → T i → FiniteDistribution (Ω i)) :
    (FiniteDistribution.uniform I).mixture
        (fun i => (P i).mixture (continuedSpecial Q i)) =
      ChildBlockMixture.mixture (fun i => (P i).mixture (Q i)) := by
  simp only [average_special]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∑ i, (1 / (Fintype.card I : ℝ)) *
      (ChildBlockMixture.special (fun j => (P j).mixture (Q j)) i).weight x) =
    (∑ i, (ChildBlockMixture.special (fun j => (P j).mixture (Q j)) i).weight x) /
      (Fintype.card I : ℝ)
  rw [← Finset.mul_sum]
  ring

end
end PerfectCompleteness.ChildBlockContinuation

end OAI
