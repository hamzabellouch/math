import OAI.Computability.PerfectCompleteness.Decoding.ChildAssemblyProjection
import OAI.Computability.PerfectCompleteness.Foundations.SourceOddListsLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CutChildCleanLawLemmas
import OAI.Computability.PerfectCompleteness.Sampling.UniformLatentSupportLemmas

namespace OAI

section

namespace PerfectCompleteness.SourceChildKernel

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays
open SourceQuestionReconstruction

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

abbrev Block (C : Type*) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  (C → squareSpace (H slots)) × Arrays slots rows

instance blockFintype (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Block C rows slots) := Fintype.ofFinite _

def zeroBlock (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) : Block C rows slots :=
  (fun _ => 0, fun _ _ => 0)

instance blockNonempty (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Block C rows slots) := ⟨zeroBlock rows slots⟩

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

abbrev Rest (i : Fin (branch n)) :=
  CleanSourceRecord.Rest (m := m) (t := t) designated i

abbrev Source (i : Fin (branch n)) := SourceTuple m t × Rest (m := m) (t := t) designated i

def tree (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    Slots branch n → SourceTuple m t :=
  CleanSourceRecord.assemble designated i s.1 s.2

def nativeSlots (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  fun leaf k => SourceKeys.slot clauses (.clause (tree designated i s leaf k).1)

def ids (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    Slots branch n → Fin t → Nat :=
  fun leaf k => (SourceClause.occurrenceVariable clauses (tree designated i s leaf k)).val

def mixedSlots (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    Bool → Slots branch n → Fin t → MixedSupport.Slot
  | false => nativeSlots clauses designated i s
  | true => ProjectedCardinality.projectedSlots (ids clauses designated i s)

theorem mixedSlots_eq_rightTuple (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (b : Bool) (leaf : Slots branch n) (k : Fin t) :
    mixedSlots clauses designated i s b leaf k =
      SourceKeys.slot clauses (rightTuple clauses b (tree designated i s leaf) k) := by
  cases b <;> rfl

abbrev Native (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :=
  Block C rows (nativeSlots clauses designated i s)

abbrev Projected (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :=
  Block C rows (ProjectedCardinality.projectedSlots (ids clauses designated i s))

abbrev Factors (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :=
  CleanTreeFactors.Factors (Fintype.card C) rows (ids clauses designated i s)

abbrev D (i : Fin (branch n)) :=
  NativeTaggedUniform.Raw (Native (C := C) (t := t) rows clauses designated i)

abbrev Raw (i : Fin (branch n)) :=
  D (C := C) (t := t) rows clauses designated i ⊕
    UniformLatent.Raw (Factors (C := C) (t := t) rows clauses designated i)

instance rawFintype (i : Fin (branch n)) :
    Fintype (Raw (C := C) (t := t) rows clauses designated i) := by
  unfold Raw
  infer_instance

def nonprojected (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    FiniteDistribution (D (C := C) (t := t) rows clauses designated i) :=
  NativeTaggedUniform.kernel (Native (C := C) (t := t) rows clauses designated i) s

def kernel (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    FiniteDistribution (Raw (C := C) (t := t) rows clauses designated i) :=
  UniformLatent.projectedKernel (Factors (C := C) (t := t) rows clauses designated i)
    (flag i) (nonprojected (C := C) (t := t) rows clauses designated i) s

def projectedEquiv (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    ((j : CleanTreeFactors.Index branch n (Fintype.card C) rows) →
      Factors (C := C) (t := t) rows clauses designated i s j) ≃
        Projected (C := C) (t := t) rows clauses designated i s :=
  (CleanTreeFactors.rawEquiv (Fintype.card C) rows (ids clauses designated i s)).trans
    (CutChildCleanLaw.rawEquiv (C := C) rows (ids clauses designated i s)).symm

def zero (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (j : CleanTreeFactors.Index branch n (Fintype.card C) rows) :
    Factors (C := C) (t := t) rows clauses designated i s j :=
  ProjectedCardinality.factorZero (CleanTreeFactors.square (Fintype.card C) rows j)
    (CleanTreeFactors.factorIds (Fintype.card C) rows (ids clauses designated i s) j)

theorem projectedEquiv_zero (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    projectedEquiv (C := C) (t := t) rows clauses designated i s (zero (C := C) (t := t) rows clauses designated i s) =
      zeroBlock rows (ProjectedCardinality.projectedSlots (ids clauses designated i s)) := rfl

theorem projectedEquiv_law (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (FiniteProduct.law (fun j => FiniteDistribution.uniform
      (Factors (C := C) (t := t) rows clauses designated i s j))).pushforward
        (projectedEquiv (C := C) (t := t) rows clauses designated i s) =
      FiniteDistribution.uniform (Projected (C := C) (t := t) rows clauses designated i s) := by
  rw [UniformLinearImage.law_uniform, FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card ((j : CleanTreeFactors.Index branch n (Fintype.card C) rows) →
    Factors (C := C) (t := t) rows clauses designated i s j) : ℝ) =
      1 / (Fintype.card (Projected (C := C) (t := t) rows clauses designated i s) : ℝ)
  rw [Fintype.card_congr (projectedEquiv (C := C) (t := t) rows clauses designated i s)]

def rawProjected (i : Fin (branch n)) : Raw (C := C) (t := t) rows clauses designated i → Bool
  | .inl _ => false
  | .inr _ => true

def rawTag (i : Fin (branch n)) :
    Raw (C := C) (t := t) rows clauses designated i → Source (m := m) (t := t) designated i :=
  NativeTaggedUniform.sourceTag (Native (C := C) (t := t) rows clauses designated i)
    (Factors (C := C) (t := t) rows clauses designated i)

theorem kernel_tag (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : Raw (C := C) (t := t) rows clauses designated i)
    (hraw : (kernel rows clauses designated flag i s).weight raw ≠ 0) :
    rawTag rows clauses designated i raw = s :=
  NativeTaggedUniform.projectedKernel_sourceTag
    (Native (C := C) (t := t) rows clauses designated i) (Factors (C := C) (t := t) rows clauses designated i)
    (flag i) s raw hraw

def decodeNative (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : D (C := C) (t := t) rows clauses designated i) : Native (C := C) (t := t) rows clauses designated i s :=
  if h : raw.1 = s then
    cast (congrArg (Native (C := C) (t := t) rows clauses designated i) h) raw.2
  else zeroBlock rows (nativeSlots clauses designated i s)

def decodeProjected (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : UniformLatent.Raw (Factors (C := C) (t := t) rows clauses designated i)) :
    Projected (C := C) (t := t) rows clauses designated i s :=
  if h : raw.1 = s then
    cast (congrArg (Projected (C := C) (t := t) rows clauses designated i) h)
      (projectedEquiv (C := C) (t := t) rows clauses designated i raw.1 raw.2)
  else zeroBlock rows (ProjectedCardinality.projectedSlots (ids clauses designated i s))

omit [Fintype C] in
@[simp] theorem decodeNative_tagged (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (x : Native (C := C) (t := t) rows clauses designated i s) :
    decodeNative rows clauses designated i s ⟨s, x⟩ = x := by
  simp [decodeNative]

@[simp] theorem decodeProjected_tagged (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (x : (j : CleanTreeFactors.Index branch n (Fintype.card C) rows) →
      Factors (C := C) (t := t) rows clauses designated i s j) :
    decodeProjected rows clauses designated i s ⟨s, x⟩ =
      projectedEquiv (C := C) (t := t) rows clauses designated i s x := by
  simp [decodeProjected]

def decodeRight (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (raw : Raw (C := C) (t := t) rows clauses designated i) →
      Block C rows (mixedSlots clauses designated i s (rawProjected rows clauses designated i raw))
  | .inl raw => decodeNative rows clauses designated i s raw
  | .inr raw => decodeProjected rows clauses designated i s raw

theorem decodeNative_law (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (nonprojected (C := C) (t := t) rows clauses designated i s).pushforward
      (decodeNative rows clauses designated i s) =
        FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s) := by
  unfold nonprojected NativeTaggedUniform.kernel
  rw [FiniteDistribution.pushforward_comp]
  simp only [decodeNative_tagged]
  change (FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s)).pushforward
    (Equiv.refl _) = _
  rw [FiniteDistribution.pushforward_equiv]
  rfl

theorem decodeProjected_law (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (UniformLatent.latentKernel (Factors (C := C) (t := t) rows clauses designated i) s).pushforward
      (decodeProjected rows clauses designated i s) =
        FiniteDistribution.uniform (Projected (C := C) (t := t) rows clauses designated i s) := by
  rw [UniformLatent.latentKernel, FiniteDistribution.pushforward_comp]
  simp only [decodeProjected_tagged]
  exact projectedEquiv_law rows clauses designated i s

theorem decodeRight_clean (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : Raw (C := C) (t := t) rows clauses designated i)
    (htag : rawTag rows clauses designated i raw = s)
    (hclean : UniformLatent.projectedZero (Factors (C := C) (t := t) rows clauses designated i)
      (zero (C := C) (t := t) rows clauses designated i) raw = true) :
    decodeRight rows clauses designated i s raw =
      zeroBlock rows (mixedSlots clauses designated i s
        (rawProjected rows clauses designated i raw)) := by
  cases raw with
  | inl raw =>
      simp only [UniformLatent.projectedZero, Bool.false_eq_true] at hclean
  | inr raw =>
      rcases raw with ⟨tag, values⟩
      change tag = s at htag
      subst tag
      change decide (∀ j, values j = zero (C := C) (t := t) rows clauses designated i s j) = true at hclean
      have hvalues : values = zero (C := C) (t := t) rows clauses designated i s :=
        funext (of_decide_eq_true hclean)
      change decodeProjected rows clauses designated i s ⟨s, values⟩ = _
      rw [hvalues, decodeProjected_tagged]
      exact projectedEquiv_zero (C := C) (t := t) rows clauses designated i s

def projection (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) (b : Bool) :
    ∀ leaf k, MixedSupport.Projection (nativeSlots clauses designated i s leaf k)
      (mixedSlots clauses designated i s b leaf k) := by
  cases b with
  | false => exact fun leaf k => .keep (nativeSlots clauses designated i s leaf k)
  | true => exact fun leaf k =>
      (SourceKeys.Step.select (clauses := clauses)
        (tree designated i s leaf k).1 (tree designated i s leaf k).2).projection

abbrev Sources := (i : Fin (branch n)) → Source (m := m) (t := t) designated i

def parentLeftSlots (sources : Sources (m := m) (t := t) designated) :
    Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  fun leaf k => nativeSlots clauses designated leaf.1 (sources leaf.1) leaf.2 k

def parentRightSlots (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  fun leaf k => mixedSlots clauses designated leaf.1 (sources leaf.1)
    (rawProjected rows clauses designated leaf.1 (raw leaf.1)) leaf.2 k

def parentProjection (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    ∀ leaf k, MixedSupport.Projection (parentLeftSlots clauses designated sources leaf k)
      (parentRightSlots rows clauses designated sources raw leaf k) :=
  fun leaf k => projection clauses designated leaf.1 (sources leaf.1)
    (rawProjected rows clauses designated leaf.1 (raw leaf.1)) leaf.2 k

def rightChildren (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    CutChildGrouping.Raw (C := C) (t := t) (parentRightSlots rows clauses designated sources raw) rows :=
  fun i => decodeRight rows clauses designated i (sources i) (raw i)

def leftChildren (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    CutChildGrouping.Raw (C := C) (t := t) (parentLeftSlots clauses designated sources) rows :=
  ChildAssemblyProjection.rawPullback rows
    (parentProjection rows clauses designated sources raw)
    (rightChildren rows clauses designated sources raw)

theorem leftChildren_apply (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i)
    (i : Fin (branch n)) :
    leftChildren rows clauses designated sources raw i =
      ChildAssemblyProjection.childPullback rows
        (parentProjection rows clauses designated sources raw) i
        (rightChildren rows clauses designated sources raw i) := rfl

theorem assemble_leftChildren (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    CutChildGrouping.assemble (parentLeftSlots clauses designated sources) rows
        (leftChildren rows clauses designated sources raw) =
      ChildAssemblyProjection.assembledPullback rows
        (parentProjection rows clauses designated sources raw)
        (CutChildGrouping.assemble (parentRightSlots rows clauses designated sources raw) rows
          (rightChildren rows clauses designated sources raw)) :=
  ChildAssemblyProjection.assemble_pullback rows
    (parentProjection rows clauses designated sources raw)
    (rightChildren rows clauses designated sources raw)

abbrev Sample := (i : Fin (branch n)) → SourceTuple m t ×
  (Rest (m := m) (t := t) designated i × Raw (C := C) (t := t) rows clauses designated i)

instance sampleFintype : Fintype (Sample (C := C) (t := t) rows clauses designated) := by
  unfold Sample
  infer_instance

def childrenLaw (μ : Fin (branch n) → FiniteDistribution (SourceTuple m t))
    (ν : (i : Fin (branch n)) → FiniteDistribution (Rest (m := m) (t := t) designated i))
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    FiniteDistribution (Sample (C := C) (t := t) rows clauses designated) :=
  UniformCleanSources.childrenLaw (Factors (C := C) (t := t) rows clauses designated) μ ν flag
    (nonprojected (C := C) (t := t) rows clauses designated)

theorem childrenLaw_tag (μ : Fin (branch n) → FiniteDistribution (SourceTuple m t))
    (ν : (i : Fin (branch n)) → FiniteDistribution (Rest (m := m) (t := t) designated i))
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hx : (childrenLaw rows clauses designated μ ν flag).weight x ≠ 0) (i : Fin (branch n)) :
    rawTag rows clauses designated i (x i).2.2 = ((x i).1, (x i).2.1) :=
  NativeTaggedUniform.childrenLaw_sourceTag
    (Native (C := C) (t := t) rows clauses designated) (Factors (C := C) (t := t) rows clauses designated)
    μ ν flag x hx i

theorem childrenLaw_clean_zero
    (μ : Fin (branch n) → FiniteDistribution (SourceTuple m t))
    (ν : (i : Fin (branch n)) → FiniteDistribution (Rest (m := m) (t := t) designated i))
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hx : (childrenLaw rows clauses designated μ ν flag).weight x ≠ 0)
    (i : Fin (branch n))
    (hclean : UniformCleanSources.childClean (Factors (C := C) (t := t) rows clauses designated)
      (zero (C := C) (t := t) rows clauses designated) i (x i).1 (x i).2.1 (x i).2.2 = true) :
    decodeRight rows clauses designated i ((x i).1, (x i).2.1) (x i).2.2 =
      zeroBlock rows (mixedSlots clauses designated i ((x i).1, (x i).2.1)
        (rawProjected rows clauses designated i (x i).2.2)) :=
  decodeRight_clean rows clauses designated i ((x i).1, (x i).2.1) (x i).2.2
    (childrenLaw_tag rows clauses designated μ ν flag x hx i) hclean

def originalLaw [NeZero m] (flag : Fin (branch n) → FiniteDistribution Bool) :
    FiniteDistribution (Sample (C := C) (t := t) rows clauses designated) :=
  childrenLaw rows clauses designated (fun _ => SourceOddLists.tupleLaw m t)
    (fun i => FiniteProduct.law (fun _ : {leaf : Slots branch n // leaf ≠ designated i} =>
      SourceOddLists.tupleLaw m t)) flag

end
end PerfectCompleteness.SourceChildKernel

end

section

namespace PerfectCompleteness.SourceChildKernelJoint

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces SourceQuestionReconstruction

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

abbrev RawTuple :=
  (i : Fin (branch n)) → SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i

def groupEquiv :
    SourceChildKernel.Sample (C := C) (t := t) rows clauses designated ≃
      SourceChildKernel.Sources (m := m) (t := t) designated ×
        RawTuple (C := C) (t := t) rows clauses designated where
  toFun x := (fun i => ((x i).1, (x i).2.1), fun i => (x i).2.2)
  invFun x := fun i => ((x.1 i).1, (x.1 i).2, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem groupEquiv_sources
    (x : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated)
    (i : Fin (branch n)) :
    (groupEquiv rows clauses designated x).1 i = ((x i).1, (x i).2.1) := rfl

@[simp] theorem groupEquiv_raw
    (x : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated)
    (i : Fin (branch n)) :
    (groupEquiv rows clauses designated x).2 i = (x i).2.2 := rfl

theorem childrenLaw_group
    (μ : Fin (branch n) → FiniteDistribution (SourceTuple m t))
    (ν : (i : Fin (branch n)) →
      FiniteDistribution (SourceChildKernel.Rest (m := m) (t := t) designated i))
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (SourceChildKernel.childrenLaw (C := C) (t := t) rows clauses designated μ ν flag).pushforward
        (groupEquiv rows clauses designated) =
      CleanConditioning.kernelJoint
        (FiniteProduct.law (fun i => (μ i).product (ν i)))
        (fun sources => FiniteProduct.law (fun i =>
          SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i (sources i))) := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨sources, raw⟩
  change (∏ i : Fin (branch n),
      (μ i).weight (sources i).1 * ((ν i).weight (sources i).2 *
        (SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i
          (sources i)).weight (raw i))) =
    (∏ i : Fin (branch n), (μ i).weight (sources i).1 * (ν i).weight (sources i).2) *
      ∏ i : Fin (branch n),
        (SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i
          (sources i)).weight (raw i)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (mul_assoc _ _ _).symm

theorem originalLaw_group [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (groupEquiv rows clauses designated) =
      CleanConditioning.kernelJoint
        (FiniteProduct.law (fun i : Fin (branch n) =>
          (SourceOddLists.tupleLaw m t).product
            (FiniteProduct.law (fun _ : {leaf : Slots branch n // leaf ≠ designated i} =>
              SourceOddLists.tupleLaw m t))))
        (fun sources => FiniteProduct.law (fun i =>
          SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i (sources i))) :=
  childrenLaw_group rows clauses designated _ _ flag

end
end PerfectCompleteness.SourceChildKernelJoint

end

section

namespace PerfectCompleteness.SourceChildKernelRate

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces ProjectedCardinality

variable {branch : Nat → Nat} {height t v m : Nat} [NeZero m]
  {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)

abbrev Factors := SourceChildKernel.Factors (C := C) (t := t) rows clauses designated
abbrev Record := UniformCleanSoundness.FullRecord
  (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
  (Factors (C := C) (t := t) rows clauses designated)
abbrev Sample := SourceChildKernel.Sample (C := C) (t := t) rows clauses designated
abbrev CleanChildren (record : Record (C := C) (t := t) rows clauses designated) :=
  UniformCleanSources.CleanIndices (Factors (C := C) (t := t) rows clauses designated) record

theorem bound_from_repetition {s L cube : Nat} [NeZero s] (hcube : 0 < cube)
    (repetition : ∀ k, ((SourceOddLists.game s clauses t).repetition k).value ≤
      (RepetitionRate.halfRate L : ℝ) ^ k)
    (event : Sample (C := C) (t := t) rows clauses designated → Bool)
    (strategies : (record : Record (C := C) (t := t) rows clauses designated) →
      Strategy (CleanChildren rows clauses designated record → Fin t → Fin m)
        (CleanChildren rows clauses designated record → Fin t → Fin v)
        (CleanChildren rows clauses designated record → OddLists.OddList s (SourceOddLists.LeftLabels t))
        (CleanChildren rows clauses designated record → OddLists.OddList s (SourceOddLists.RightLabels t)))
    (inclusion : ∀ record x,
      UniformCleanSources.recordEvent (Factors (C := C) (t := t) rows clauses designated)
        (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record x = true →
      event x = true →
      (IndexedRepetition.game (SourceOddLists.game s clauses t)
        (CleanChildren rows clauses designated record)).wins (strategies record)
          (fun i => (x i.val).1) = true) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated
      (fun _ => ProjectedCleanRate.projectionFlag cube hcube)).probability event ≤
      (1 - ProjectedCleanRate.coefficient L branch height t (Fintype.card C) rows /
        (cube : ℝ) ^ 2) ^ (branch height) := by
  let restLaw := fun i : Fin (branch height) => FiniteProduct.law
    (fun _ : {leaf : Slots branch height // leaf ≠ designated i} =>
      SourceOddLists.tupleLaw m t)
  have bound := UniformCleanSoundness.source_soundness
    (Factors (C := C) (t := t) rows clauses designated)
    (SourceOddLists.game s clauses t) restLaw
    (fun _ => ProjectedCleanRate.projectionFlag cube hcube)
    (SourceChildKernel.nonprojected (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
    (fun _ => shapeCardinality branch t
      (CleanTreeFactors.height (Fintype.card C) rows)
      (CleanTreeFactors.square (Fintype.card C) rows))
    (fun i source j => factor_card_eq
      (CleanTreeFactors.square (Fintype.card C) rows j)
      (CleanTreeFactors.factorIds (Fintype.card C) rows
        (SourceChildKernel.ids clauses designated i source) j) (fun _ _ => 0))
    event (RepetitionRate.halfRate L : ℝ) repetition strategies inclusion
  have hoccurrences : (SourceOddLists.game s clauses t).occurrences =
      SourceOddLists.tupleLaw m t := rfl
  rw [hoccurrences] at bound
  have hbase :
      1 - (1 - (RepetitionRate.halfRate L : ℝ)) *
        (ProjectedCleanRate.projectionDensity cube *
          ProjectedCleanRate.zeroProbability branch height t (Fintype.card C) rows) =
      1 - ProjectedCleanRate.coefficient L branch height t (Fintype.card C) rows /
        (cube : ℝ) ^ 2 := by
    rw [ProjectedCleanRate.coefficient_eq]
    unfold ProjectedCleanRate.projectionDensity
    ring
  calc
    _ ≤ ∏ _i : Fin (branch height),
        (1 - (1 - (RepetitionRate.halfRate L : ℝ)) *
          (ProjectedCleanRate.projectionDensity cube *
            ProjectedCleanRate.zeroProbability branch height t (Fintype.card C) rows)) := by
      simpa only [SourceChildKernel.originalLaw, SourceChildKernel.childrenLaw, Factors, restLaw,
        ProjectedCleanRate.projectionFlag_true, ProjectedCleanRate.zeroProbability] using bound
    _ = _ := by
      simp only [hbase, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem amplified_bound {s L cube : Nat} [NeZero s]
    (γ : ℚ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (ht : t = SourceOddLists.repetitionLength γ s hγ hγ1)
    (hcube : 0 < cube) (gap : SourceAmplification.ClauseGap clauses γ)
    (hL : 0 < L) (alphabet : SourceOddLists.alphabetLog s t ≤ L)
    (event : Sample (C := C) (t := t) rows clauses designated → Bool)
    (strategies : (record : Record (C := C) (t := t) rows clauses designated) →
      Strategy (CleanChildren rows clauses designated record → Fin t → Fin m)
        (CleanChildren rows clauses designated record → Fin t → Fin v)
        (CleanChildren rows clauses designated record → OddLists.OddList s (SourceOddLists.LeftLabels t))
        (CleanChildren rows clauses designated record → OddLists.OddList s (SourceOddLists.RightLabels t)))
    (inclusion : ∀ record x,
      UniformCleanSources.recordEvent (Factors (C := C) (t := t) rows clauses designated)
        (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record x = true →
      event x = true →
      (IndexedRepetition.game (SourceOddLists.game s clauses t)
        (CleanChildren rows clauses designated record)).wins (strategies record)
          (fun i => (x i.val).1) = true) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated
      (fun _ => ProjectedCleanRate.projectionFlag cube hcube)).probability event ≤
      (1 - ProjectedCleanRate.coefficient L branch height t (Fintype.card C) rows /
        (cube : ℝ) ^ 2) ^ (branch height) := by
  apply bound_from_repetition rows clauses designated hcube _ event strategies inclusion
  subst t
  exact SourceOddLists.repetition_halfRate clauses γ hγ hγ1 gap hL alphabet

end
end PerfectCompleteness.SourceChildKernelRate

end

end OAI
