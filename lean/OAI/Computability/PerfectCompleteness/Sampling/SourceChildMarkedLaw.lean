import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionKernelJoint
import OAI.Computability.PerfectCompleteness.Foundations.MultiplicationFormInjectiveLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutCallsLemmas
import OAI.Computability.PerfectCompleteness.Sampling.ChildCallNumberingLaws
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildKernelMarginalLemmas

namespace OAI

section

namespace PerfectCompleteness.SourceChildMarkedLaw

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays SourceChildKernel
open scoped Classical

noncomputable section

private theorem uniform_equiv {A B : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (e : A ≃ B) :
    (FiniteDistribution.uniform A).pushforward e = FiniteDistribution.uniform B := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card A : ℝ) = 1 / (Fintype.card B : ℝ)
  rw [Fintype.card_congr e]

private theorem kernelJoint_map {S A B : Type*}
    [Fintype S] [Fintype A] [Fintype B]
    (μ : FiniteDistribution S) (P : S → FiniteDistribution A) (f : A → B) :
    (CleanConditioning.kernelJoint μ P).pushforward (fun x => (x.1, f x.2)) =
      CleanConditioning.kernelJoint μ (fun s => (P s).pushforward f) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, CleanConditioning.probability_kernelJoint,
    CleanConditioning.probability_kernelJoint]
  simp only [FiniteDistribution.probability_pushforward]

private theorem kernelJoint_observe {S A B : Type*}
    [Fintype S] [Fintype A] [Fintype B]
    (μ : FiniteDistribution S) (P : S → FiniteDistribution A) (f : S × A → B) :
    (CleanConditioning.kernelJoint μ P).pushforward f =
      μ.mixture (fun s => (P s).pushforward (fun a => f (s, a))) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, CleanConditioning.probability_kernelJoint,
    FiniteDistribution.probability_mixture]
  simp only [FiniteDistribution.probability_pushforward]

private theorem joint_product_observe {S Z A : Type*} {Y : S → Type*}
    [Fintype S] [Fintype Z] [Fintype A] [∀ s, Fintype (Y s)]
    (μ : FiniteDistribution S) (ν : FiniteDistribution Z)
    (P : S → Z → FiniteDistribution A) (f : (s : S) → Z × A → Y s) :
    (CleanConditioning.kernelJoint (μ.product ν) (fun x => P x.1 x.2)).pushforward
        (fun x => (⟨x.1.1, f x.1.1 (x.1.2, x.2)⟩ : Σ s, Y s)) =
      CompletionSoundness.sigmaLaw μ
        (fun s => (CleanConditioning.kernelJoint ν (P s)).pushforward (f s)) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, CleanConditioning.probability_kernelJoint,
    CompletionSoundness.sigmaLaw_probability]
  simp only [FiniteDistribution.product, FiniteDistribution.expectation, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [FiniteDistribution.probability_pushforward, CleanConditioning.probability_kernelJoint,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact mul_assoc _ _ _

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def projectedLaw (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    FiniteDistribution (Native (C := C) (t := t) rows clauses designated i s) :=
  (FiniteDistribution.uniform (Projected (C := C) (t := t) rows clauses designated i s)).pushforward
    (SourceChildNativeLaw.pullback rows clauses designated i s true)

def markedChild (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : Raw (C := C) (t := t) rows clauses designated i) :
    Bool × Native (C := C) (t := t) rows clauses designated i s :=
  (rawProjected rows clauses designated i raw,
    SourceChildNativeLaw.decodeLeft rows clauses designated i s raw)

theorem kernel_markedChild (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (kernel (C := C) (t := t) rows clauses designated flag i s).pushforward
        (markedChild rows clauses designated i s) =
      CleanConditioning.kernelJoint (flag i) (fun b => if b then
        projectedLaw (C := C) (t := t) rows clauses designated i s
        else FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s)) := by
  calc
    _ = ((kernel (C := C) (t := t) rows clauses designated flag i s).pushforward
        (SourceChildKernelLaw.physical rows clauses designated i s)).pushforward
          (fun x => (x.1, SourceChildNativeLaw.physicalLeft rows clauses designated i s x)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = CleanConditioning.kernelJoint (flag i) (fun b =>
        (FiniteDistribution.uniform (Block C rows (mixedSlots clauses designated i s b))).pushforward
          (SourceChildNativeLaw.pullback rows clauses designated i s b)) := by
      rw [SourceChildKernelLaw.kernel_physical]
      exact MarkedKernelProduct.physical_marked (flag i)
        (fun b => FiniteDistribution.uniform (Block C rows (mixedSlots clauses designated i s b)))
        (SourceChildNativeLaw.pullback rows clauses designated i s)
    _ = _ := by
      apply congrArg (CleanConditioning.kernelJoint (flag i))
      funext b
      cases b with
      | false =>
          have hf : SourceChildNativeLaw.pullback (C := C) rows clauses designated i s false =
              (id : Native (C := C) (t := t) rows clauses designated i s → _) :=
            funext (SourceChildNativeLaw.pullback_false rows clauses designated i s)
          change (FiniteDistribution.uniform
            (Native (C := C) (t := t) rows clauses designated i s)).pushforward
              (SourceChildNativeLaw.pullback rows clauses designated i s false) = _
          rw [hf, FiniteDistribution.pushforward_id]
          rfl
      | true => rfl

abbrev Questions := SourceQuestionPositionSplit.Questions
  (branch := branch) (n := n) (t := t) (m := m)

abbrev Choice := SourceQuestionPositionSplit.ChildPositions (branch := branch) (n := n) (t := t)

def childSource (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    Source (m := m) (t := t) designated i :=
  SourceQuestionPositionSplit.join designated q (fun leaf k => z leaf.2 k) i

def questionSlots (q : Questions (branch := branch) (n := n) (t := t) (m := m)) :
    Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  sourceSlots clauses (PreliminarySampler.endpoints q)

theorem nativeSlots_childSource
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    nativeSlots clauses designated i (childSource designated q i z) =
      childSlots (questionSlots clauses q) i :=
  congrArg (fun slots => childSlots slots i)
    (SourceQuestionPositionSplit.parentLeftSlots_join clauses designated q (fun leaf k => z leaf.2 k))

theorem childSource_sources
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (zs : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (i : Fin (branch n)) :
    childSource designated q i (zs i) = SourceQuestionKernelJoint.sources designated q zs i := rfl

def nativeEquiv (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    Native (C := C) (t := t) rows clauses designated i (childSource designated q i z) ≃
      CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i :=
  Equiv.cast (congrArg (Block C rows) (nativeSlots_childSource clauses designated q i z))

def projectedSlots (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  mixedSlots clauses designated i (childSource designated q i z) true

def questionProjection
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    ∀ leaf k, MixedSupport.Projection (childSlots (questionSlots clauses q) i leaf k)
      (projectedSlots clauses designated q i z leaf k) :=
  cast (congrArg
    (fun slots : Slots branch n → Fin t → MixedSupport.Slot =>
      ∀ leaf k, MixedSupport.Projection (slots leaf k)
        (projectedSlots clauses designated q i z leaf k))
    (nativeSlots_childSource clauses designated q i z))
      (projection clauses designated i (childSource designated q i z) true)

omit [Fintype C] in
theorem nativeEquiv_pullback
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t))
    (block : Projected (C := C) (t := t) rows clauses designated i (childSource designated q i z)) :
    nativeEquiv rows clauses designated q i z
        (SourceChildNativeLaw.pullback rows clauses designated i (childSource designated q i z) true block) =
      ChildCallNumbering.pullback rows (questionProjection clauses designated q i z) block :=
  ChildCallNumbering.pullback_cast rows (nativeSlots_childSource clauses designated q i z)
    (projection clauses designated i (childSource designated q i z) true) block

omit [Fintype C] in
theorem nativeEquiv_pullback_call
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t))
    (block : Projected (C := C) (t := t) rows clauses designated i (childSource designated q i z))
    (call : C) (x : Domain (childSlots (questionSlots clauses q) i)) :
    ((nativeEquiv rows clauses designated q i z
      (SourceChildNativeLaw.pullback rows clauses designated i (childSource designated q i z) true block)).1 call).val x =
        (block.1 call).val (sourceProjection (questionProjection clauses designated q i z) x) := by
  rw [nativeEquiv_pullback]; rfl

omit [Fintype C] in
theorem nativeEquiv_pullback_arrays
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t))
    (block : Projected (C := C) (t := t) rows clauses designated i (childSource designated q i z))
    (x : Domain (childSlots (questionSlots clauses q) i)) :
    fullJoint (nativeEquiv rows clauses designated q i z
      (SourceChildNativeLaw.pullback rows clauses designated i (childSource designated q i z) true block)).2 x =
        fullJoint block.2 (sourceProjection (questionProjection clauses designated q i z) x) := by
  rw [nativeEquiv_pullback]; rfl

def replacementAt (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    FiniteDistribution (CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i) :=
  (projectedLaw (C := C) (t := t) rows clauses designated i (childSource designated q i z)).pushforward
    (nativeEquiv rows clauses designated q i z)

def replacementLaws (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) :
    FiniteDistribution (CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i) :=
  (FiniteDistribution.uniform (Choice (branch := branch) (n := n) (t := t))).mixture
    (replacementAt rows clauses designated q i)

theorem replacementAt_eq_liftedLaw
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    replacementAt (C := C) rows clauses designated q i z =
      ChildCallNumberingLaws.liftedLaw (C := C) rows (questionProjection clauses designated q i z) := by
  let μ : FiniteDistribution
      (Projected (C := C) (t := t) rows clauses designated i (childSource designated q i z)) :=
    FiniteDistribution.uniform _
  let f : Projected (C := C) (t := t) rows clauses designated i (childSource designated q i z) →
      Native (C := C) (t := t) rows clauses designated i (childSource designated q i z) :=
    fun block => SourceChildNativeLaw.pullback rows clauses designated i
      (childSource designated q i z) true block
  let g : Native (C := C) (t := t) rows clauses designated i (childSource designated q i z) →
      CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i :=
    nativeEquiv rows clauses designated q i z
  exact (FiniteDistribution.pushforward_comp μ f g).trans
    (congrArg (fun k : Projected (C := C) (t := t) rows clauses designated i
        (childSource designated q i z) →
        CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i => μ.pushforward k)
      (funext fun block => nativeEquiv_pullback rows clauses designated q i z block))

theorem replacementLaws_eq
    (q : Questions (branch := branch) (n := n) (t := t) (m := m)) :
    replacementLaws (C := C) rows clauses designated q =
      ChildCallNumberingLaws.replacementLaws (C := C) rows (childSlots (questionSlots clauses q))
        (projectedSlots clauses designated q) (questionProjection clauses designated q)
        (fun _ => FiniteDistribution.uniform (Choice (branch := branch) (n := n) (t := t))) := by
  funext i
  unfold replacementLaws ChildCallNumberingLaws.replacementLaws ChildCallNumberingLaws.mixtureLaw
  apply congrArg (FiniteDistribution.mixture
    (FiniteDistribution.uniform (Choice (branch := branch) (n := n) (t := t))))
  funext z
  exact replacementAt_eq_liftedLaw rows clauses designated q i z

def questionMarkedChild
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t))
    (raw : Raw (C := C) (t := t) rows clauses designated i) :
    Bool × CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i :=
  (rawProjected rows clauses designated i raw,
    nativeEquiv rows clauses designated q i z
      (SourceChildNativeLaw.decodeLeft rows clauses designated i (childSource designated q i z) raw))

theorem kernel_questionMarkedChild
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    (kernel (C := C) (t := t) rows clauses designated flag i (childSource designated q i z)).pushforward
        (questionMarkedChild rows clauses designated q i z) =
      CleanConditioning.kernelJoint (flag i) (fun b => if b then
        replacementAt (C := C) rows clauses designated q i z
        else FiniteDistribution.uniform (CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i)) := by
  calc
    _ = ((kernel (C := C) (t := t) rows clauses designated flag i (childSource designated q i z)).pushforward
        (markedChild rows clauses designated i (childSource designated q i z))).pushforward
          (fun x => (x.1, nativeEquiv rows clauses designated q i z x.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by
      rw [kernel_markedChild, kernelJoint_map]
      apply congrArg (CleanConditioning.kernelJoint (flag i))
      funext b
      cases b with
      | false => exact uniform_equiv (nativeEquiv rows clauses designated q i z)
      | true => rfl

abbrev Marked (q : Questions (branch := branch) (n := n) (t := t) (m := m)) :=
  (Fin (branch n) → Bool) × CutChildGrouping.Raw (C := C) (questionSlots clauses q) rows

def markedBlocks (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (zs : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (raw : SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated) :
    Marked (C := C) rows clauses q :=
  MarkedKernelProduct.markEquiv (fun i => questionMarkedChild rows clauses designated q i (zs i) (raw i))

theorem kernels_markedBlocks
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (zs : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (FiniteProduct.law (fun i => kernel (C := C) (t := t) rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ') i
        (SourceQuestionKernelJoint.sources designated q zs i))).pushforward
          (markedBlocks rows clauses designated q zs) =
      SparseReplacement.markedLaw
        (fun i => FiniteDistribution.uniform (CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i))
        (fun i => replacementAt rows clauses designated q i (zs i)) β hβ hβ' := by
  let P : (i : Fin (branch n)) → FiniteDistribution (Raw (C := C) (t := t) rows clauses designated i) :=
    fun i => kernel rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ') i
      (SourceQuestionKernelJoint.sources designated q zs i)
  let f : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i →
      Bool × CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i :=
    fun i => questionMarkedChild rows clauses designated q i (zs i)
  let e : ((i : Fin (branch n)) →
      Bool × CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i) ≃
      Marked (C := C) rows clauses q := MarkedKernelProduct.markEquiv
  calc
    _ = ((FiniteProduct.law P).pushforward (fun raw i => f i (raw i))).pushforward e :=
      (FiniteDistribution.pushforward_comp (FiniteProduct.law P)
        (fun raw i => f i (raw i)) e).symm
    _ = (FiniteProduct.law (fun i => (P i).pushforward (f i))).pushforward e :=
      congrArg (fun law : FiniteDistribution ((i : Fin (branch n)) →
          Bool × CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i) =>
          law.pushforward e)
        (FiniteProduct.pushforward_map P f)
    _ = (FiniteProduct.law (fun i => CleanConditioning.kernelJoint
        (ProjectionPosterior.bernoulli β hβ hβ') (fun b => if b then
          replacementAt (C := C) rows clauses designated q i (zs i)
          else FiniteDistribution.uniform
            (CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i)))).pushforward e :=
      congrArg (fun laws : (i : Fin (branch n)) → FiniteDistribution
          (Bool × CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i) =>
          (FiniteProduct.law laws).pushforward e)
        (funext fun i => kernel_questionMarkedChild rows clauses designated
          (fun _ => ProjectionPosterior.bernoulli β hβ hβ') q i (zs i))
    _ = _ := MarkedKernelProduct.marked_product _ _ β hβ hβ'

theorem conditional_markedLaw
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (CleanConditioning.kernelJoint
      (FiniteProduct.law (fun _ : Fin (branch n) =>
        FiniteDistribution.uniform (Choice (branch := branch) (n := n) (t := t))))
      (fun zs => FiniteProduct.law (fun i => kernel (C := C) (t := t) rows clauses designated
        (fun _ => ProjectionPosterior.bernoulli β hβ hβ') i
          (SourceQuestionKernelJoint.sources designated q zs i)))).pushforward
            (fun x => markedBlocks rows clauses designated q x.1 x.2) =
      SparseReplacement.markedLaw
        (fun i => FiniteDistribution.uniform (CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i))
        (replacementLaws rows clauses designated q) β hβ hβ' := by
  rw [kernelJoint_observe]
  simp only [kernels_markedBlocks]
  exact MarkedKernelProduct.mixture_markedLaw _ _ _ β hβ hβ'

abbrev Observation :=
  Σ q : Questions (branch := branch) (n := n) (t := t) (m := m),
    Marked (C := C) rows clauses q

def observe (sample : Sample (C := C) (t := t) rows clauses designated) :
    Observation (branch := branch) (n := n) (C := C) (t := t) rows clauses :=
  let grouped := SourceQuestionKernelJoint.groupEquiv rows clauses designated sample
  ⟨grouped.1.1, markedBlocks rows clauses designated grouped.1.1 grouped.1.2 grouped.2⟩

@[simp] theorem observe_mask
    (sample : Sample (C := C) (t := t) rows clauses designated) (i : Fin (branch n)) :
    (observe rows clauses designated sample).2.1 i =
      rawProjected rows clauses designated i (sample i).2.2 := rfl

theorem original_marked_law [NeZero m]
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (originalLaw (C := C) (t := t) rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ')).pushforward
        (observe rows clauses designated) =
      CompletionSoundness.sigmaLaw
        (PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m))
        (fun q => SparseReplacement.markedLaw
          (fun i => FiniteDistribution.uniform
            (CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i))
          (replacementLaws rows clauses designated q) β hβ hβ') := by
  unfold observe
  rw [← FiniteDistribution.pushforward_comp
    (originalLaw (C := C) (t := t) rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ'))
    (SourceQuestionKernelJoint.groupEquiv rows clauses designated)
    (fun x => (⟨x.1.1, markedBlocks rows clauses designated x.1.1 x.1.2 x.2⟩ :
      Observation (branch := branch) (n := n) (C := C) (t := t) rows clauses)),
    SourceQuestionKernelJoint.originalLaw_group]
  exact (joint_product_observe
    (S := Questions (branch := branch) (n := n) (t := t) (m := m))
    (Z := SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (A := SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated)
    (Y := fun q => Marked (C := C) rows clauses q)
    (PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m))
    (FiniteProduct.law (fun _ : Fin (branch n) =>
      FiniteDistribution.uniform (Choice (branch := branch) (n := n) (t := t))))
    (fun q zs => FiniteProduct.law (fun i => kernel (C := C) (t := t) rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ') i
      (SourceQuestionKernelJoint.sources designated q zs i)))
    (fun q x => markedBlocks rows clauses designated q x.1 x.2)).trans
      (congrArg (CompletionSoundness.sigmaLaw
        (PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m)))
          (funext fun q => conditional_markedLaw rows clauses designated q β hβ hβ'))

theorem original_extended_marked_law [NeZero m] {root : Nat}
    (repeats : Nat → Nat) (p : DescendantSpaces.Path branch root (n + 1))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (originalLaw (C := Option (WholeCutCalls.Index rows repeats p)) (t := t)
      rows clauses designated (fun _ => ProjectionPosterior.bernoulli β hβ hβ')).pushforward
        (observe rows clauses designated) =
      CompletionSoundness.sigmaLaw
        (PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m))
        (fun q => SparseReplacement.markedLaw
          (fun i => FiniteDistribution.uniform
            (CutChildGrouping.Child (C := Option (WholeCutCalls.Index rows repeats p))
              (questionSlots clauses q) rows i))
          (replacementLaws rows clauses designated q) β hβ hβ') :=
  original_marked_law rows clauses designated β hβ hβ'

end
end PerfectCompleteness.SourceChildMarkedLaw

end

end OAI
