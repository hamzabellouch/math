import OAI.Computability.PerfectCompleteness.Construction.SourcePhysicalChildExpectation
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionPhysicalHigh
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalHighEvent
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalRawChildren

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalHighAverage

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

private theorem mpr_heq {α β : Sort _} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev suffix := CleanRightDecoder.suffix upper (CleanPhysicalDecoderLaw.lower S)
  S.cut (CleanDecoderContext.lowerHeight upper d)

include S in
theorem suffix_proper : h + 1 < Nodes.height upper :=
  CleanRightDecoder.suffix_proper upper (CleanPhysicalDecoderLaw.lower S)
    S.cut (CleanDecoderContext.lowerHeight upper d)

variable (hbranch : ∀ k < n, 0 < branch k)
  (hnode : WholeArrayInteriorExterior.upperNode (CleanDecoderRate.path S) =
    HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
  {Original : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Original slots)]
  (F : OriginalDecoderMark.Family branch rows n t Original) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (direction : BucketSampler.Direction (rows (h + 1))) (threshold : ℝ) (s : Nat)

abbrev nativeDirection :=
  (ProjectedFiberRawPair.direction (CleanDecoderRate.path S) upper (h + 1) d hnode direction).val

def tapeStatistic
    (left right : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (projection : ∀ leaf k, MixedSupport.Projection (left leaf k) (right leaf k))
    (tape : WholeCutSampler.Tape rows repeats (CleanDecoderRate.path S)
      (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside right)) : ℝ :=
  LowerProjectedOriginalSuccess.kernelSuccess (repeats := repeats) (CleanDecoderRate.path S)
    (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside left)
    (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside right)
    (CutProjectionAssembly.fillProjection (CleanDecoderRate.path S) S.outside left right projection)
    upper (h + 1) hbranch d hnode direction A S.cut σ
    (OriginalDecoderMark.mark F upper (h + 1) κ
      (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside left)) ρ threshold s
    (WholeCutSubtree.knownBucketsAtNode rows repeats
      (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside right)
      upper (suffix S) (suffix_proper S) (LinearMap.ker A) tape)
    (WholeCutSampler.evaluate rows repeats (CleanDecoderRate.path S)
      (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside right) tape)

def childStatistic
    (left right : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (projection : ∀ leaf k, MixedSupport.Projection (left leaf k) (right leaf k))
    (children : CutChildGrouping.Raw (C := CleanDecoderRate.Calls S) right rows) : ℝ :=
  tapeStatistic S hbranch hnode F κ σ r ρ A direction threshold s left right projection
    (CleanPhysicalReplay.physicalTape rows repeats (CleanDecoderRate.path S)
      S.outside S.placeholder right S.exterior children)

private theorem childStatistic_congr
    (left left' right : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (hl : left = left')
    (projection : ∀ leaf k, MixedSupport.Projection (left leaf k) (right leaf k))
    (projection' : ∀ leaf k, MixedSupport.Projection (left' leaf k) (right leaf k))
    (hp : ∀ leaf k, HEq (projection leaf k) (projection' leaf k))
    (children : CutChildGrouping.Raw (C := CleanDecoderRate.Calls S) right rows) :
    childStatistic S hbranch hnode F κ σ r ρ A direction threshold s
        left right projection children =
      childStatistic S hbranch hnode F κ σ r ρ A direction threshold s
        left' right projection' children := by
  cases hl
  have he : projection = projection' :=
    funext (fun leaf => funext (fun k => eq_of_heq (hp leaf k)))
  cases he
  rfl

theorem rightInput_eq (x : CleanDecoderRate.Sample S) :
    CleanPhysicalDecoderLaw.rightInput S (LinearMap.ker A)
        (nativeDirection S hnode direction) x =
      LowerCutOwnInput.ofArrays (CleanNativeReplay.rightSlots S x) rows upper
        (CleanPhysicalDecoderLaw.lower S) (LinearMap.ker A)
        (nativeDirection S hnode direction)
        (WholeCutSubtree.knownBucketsAtNode rows repeats (CleanNativeReplay.rightSlots S x)
          upper (suffix S) (suffix_proper S) (LinearMap.ker A)
          (CleanNativeReplay.rightTape S x))
        (CleanPhysicalDecoderLaw.rightArrays S x) := by
  have hk := WholeCutSubtree.knownBuckets_eq_original rows repeats (Nodes.path upper)
    (suffix S) (suffix_proper S) (CleanNativeReplay.rightSlots S x)
    (LinearMap.ker A) (CleanNativeReplay.rightTape S x)
  exact congrArg
    (fun known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
        OwnInputReference.UpperSpace (CleanNativeReplay.rightSlots S x) upper =>
      CleanPhysicalDecoderLaw.inputOfArrays (CleanNativeReplay.rightSlots S x)
        upper (CleanPhysicalDecoderLaw.lower S) (LinearMap.ker A)
        (nativeDirection S hnode direction) known (CleanPhysicalDecoderLaw.rightArrays S x))
    hk.symm

theorem physical_probability_eq (x : CleanDecoderRate.Sample S) :
    (CleanPhysicalDecoderLaw.pairKernel S F κ σ r ρ A (LinearMap.ker A)
      (nativeDirection S hnode direction) threshold x).probability
        (CleanPhysicalHighEvent.highEvent S hbranch s x) =
      childStatistic S hbranch hnode F κ σ r ρ A direction threshold s
        (CleanPhysicalReplay.leftInside rows repeats (CleanDecoderRate.path S)
          S.clauses S.designated x)
        (CleanPhysicalReplay.rightInside rows repeats (CleanDecoderRate.path S)
          S.clauses S.designated x)
        (SourceChildKernel.parentProjection rows S.clauses S.designated
          (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2))
        (CleanPhysicalReplay.rightBlocks rows repeats (CleanDecoderRate.path S)
          S.clauses S.designated x) := by
  have ha := CleanPhysicalCanonicalQuery.arrays_pullback rows repeats (CleanDecoderRate.path S)
    S.outside S.placeholder S.clauses S.designated x S.exterior
  change CleanPhysicalDecoderLaw.leftArrays S x = _ at ha
  unfold childStatistic tapeStatistic LowerProjectedOriginalSuccess.kernelSuccess
  unfold CleanPhysicalDecoderLaw.pairKernel CleanPhysicalDecoderLaw.leftLaw
    CleanPhysicalDecoderLaw.rightLaw
  rw [rightInput_eq S hnode r A direction x]
  unfold CleanPhysicalDecoderLaw.adviceLaw
  rw [ha]
  rfl

def sourceStatistic
    (sources : SourceChildKernel.Sources (m := m) (t := t) S.designated)
    (observed : Σ flags : SourceProjectedTag.Flags (branch := branch) (n := h),
      CutChildGrouping.Raw (C := CleanDecoderRate.Calls S)
        (SourcePhysicalTaggedChildren.slots S.clauses S.designated sources flags) rows) : ℝ :=
  childStatistic S hbranch hnode F κ σ r ρ A direction threshold s
    (SourceChildKernel.parentLeftSlots S.clauses S.designated sources)
    (SourcePhysicalTaggedChildren.slots S.clauses S.designated sources observed.1)
    (fun leaf k => SourceChildKernel.projection S.clauses S.designated leaf.1
      (sources leaf.1) (observed.1 leaf.1) leaf.2 k) observed.2

def questionStatistic
    (q : PreliminarySampler.Questions branch (h + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := h) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := h))
    (children : CutChildGrouping.Raw (C := CleanDecoderRate.Calls S)
      (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags) rows) : ℝ :=
  childStatistic S hbranch hnode F κ σ r ρ A direction threshold s
    (SourceProjectedTag.originalSlots S.clauses q)
    (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags)
    (SourceProjectedTag.projection S.clauses S.designated q choices flags) children

private theorem sourceStatistic_eq_question
    (q : PreliminarySampler.Questions branch (h + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := h) (t := t))
    (observed : Σ flags : SourceProjectedTag.Flags (branch := branch) (n := h),
      CutChildGrouping.Raw (C := CleanDecoderRate.Calls S)
        (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags) rows) :
    sourceStatistic S hbranch hnode F κ σ r ρ A direction threshold s
        (SourceQuestionKernelJoint.sources S.designated q choices) observed =
      questionStatistic S hbranch hnode F κ σ r ρ A direction threshold s
        q choices observed.1 observed.2 := by
  apply childStatistic_congr S hbranch hnode F κ σ r ρ A direction threshold s
    _ _ _ (SourceProjectedTag.parentLeftSlots_sources S.clauses S.designated q choices)
  intro leaf k
  symm
  unfold SourceProjectedTag.projection
  dsimp only [id]
  exact mpr_heq _ _

theorem physical_probability_eq_observed (x : CleanDecoderRate.Sample S) :
    (CleanPhysicalDecoderLaw.pairKernel S F κ σ r ρ A (LinearMap.ker A)
      (nativeDirection S hnode direction) threshold x).probability
        (CleanPhysicalHighEvent.highEvent S hbranch s x) =
      let q := SourceQuestionRawSwap.insideQuestions rows S.clauses S.designated x
      let choices := SourceQuestionRawSwap.positions rows S.clauses S.designated x
      let observed := SourcePhysicalChildExpectation.observe rows S.clauses S.designated q choices
        (SourceQuestionRawSwap.raw rows S.clauses S.designated x)
      questionStatistic S hbranch hnode F κ σ r ρ A direction threshold s
        q choices observed.1 observed.2 := by
  let q := SourceQuestionRawSwap.insideQuestions rows S.clauses S.designated x
  let choices := SourceQuestionRawSwap.positions rows S.clauses S.designated x
  let observed := SourcePhysicalChildExpectation.observe rows S.clauses S.designated q choices
    (SourceQuestionRawSwap.raw rows S.clauses S.designated x)
  have hread := congrArg
    (fun sources : SourceChildKernel.Sources (m := m) (t := t) S.designated =>
      sourceStatistic S hbranch hnode F κ σ r ρ A direction threshold s sources
        (SourcePhysicalTaggedChildren.observe rows S.clauses S.designated sources
          (SourceQuestionRawSwap.raw rows S.clauses S.designated x)))
    (SourceQuestionRawSwap.sources_insideQuestions_positions rows S.clauses S.designated x)
  exact (physical_probability_eq S hbranch hnode F κ σ r ρ A direction threshold s x).trans
    (hread.symm.trans (sourceStatistic_eq_question S hbranch hnode F κ σ r ρ A
      direction threshold s q choices observed))

theorem questionStatistic_expectation
    (q : PreliminarySampler.Questions branch (h + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := h) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := h)) :
    (CutChildGrouping.rawLaw (C := CleanDecoderRate.Calls S)
      (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags) rows).expectation
        (questionStatistic S hbranch hnode F κ σ r ρ A direction threshold s q choices flags) =
      SourceQuestionPhysicalHigh.success S.outside S.placeholder S.clauses S.designated
        q choices flags upper (suffix S) (suffix_proper S) (h + 1) hbranch d hnode A S.cut σ
        (OriginalDecoderMark.mark F upper (h + 1) κ
          (SourceQuestionPhysicalHigh.originalSlots (CleanDecoderRate.path S) S.outside S.clauses q))
        ρ threshold S.exterior direction s := by
  exact CleanPhysicalRawChildren.expectation_lowerTape rows repeats S.outside S.placeholder
    (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags)
    upper (suffix S) S.exterior
    (tapeStatistic S hbranch hnode F κ σ r ρ A direction threshold s
      (SourceProjectedTag.originalSlots S.clauses q)
      (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags)
      (SourceProjectedTag.projection S.clauses S.designated q choices flags))

theorem mean_probability_eq (cube : Nat) (hcube : 0 < cube) :
    (CleanDecoderPairLaw.pairLaw S σ (CleanPhysicalDecoderLaw.useful S F κ)
      r ρ A (LinearMap.ker A) (nativeDirection S hnode direction) threshold cube hcube).probability
        (fun z => DecoderRankSplit.highAgrees S hbranch s z.1 z.2) =
      (PreliminarySampler.questionsLaw
        (branch := branch) (n := h + 1) (t := t) (m := m)).expectation
        (fun q => (SourceProjectedTag.positionLaw
          (branch := branch) (n := h) (t := t)).expectation
          (fun choices => (SourceProjectedTag.flagLaw
            (fun _ : Fin (branch h) => ProjectedCleanRate.projectionFlag cube hcube)).expectation
            (fun flags => SourceQuestionPhysicalHigh.success
              S.outside S.placeholder S.clauses S.designated q choices flags
              upper (suffix S) (suffix_proper S) (h + 1) hbranch d hnode A S.cut σ
              (OriginalDecoderMark.mark F upper (h + 1) κ
                (SourceQuestionPhysicalHigh.originalSlots
                  (CleanDecoderRate.path S) S.outside S.clauses q))
              ρ threshold S.exterior direction s))) := by
  rw [← CleanPhysicalHighEvent.mean_probability_eq S hbranch F κ σ r ρ A
    (LinearMap.ker A) (nativeDirection S hnode direction) threshold cube hcube s]
  have hsample := FiniteDistribution.expectation_congr (CleanDecoderRate.rawLaw S cube hcube)
    (physical_probability_eq_observed S hbranch hnode F κ σ r ρ A direction threshold s)
  refine hsample.trans ?_
  rw [show CleanDecoderRate.rawLaw S cube hcube =
    SourceChildKernel.originalLaw (C := CleanDecoderRate.Calls S) (t := t)
      rows S.clauses S.designated
      (fun _ => ProjectedCleanRate.projectionFlag cube hcube) from rfl]
  rw [SourcePhysicalChildExpectation.originalLaw_expectation rows S.clauses S.designated
    (fun _ => ProjectedCleanRate.projectionFlag cube hcube)
    (questionStatistic S hbranch hnode F κ σ r ρ A direction threshold s)]
  apply FiniteDistribution.expectation_congr
  intro q
  apply FiniteDistribution.expectation_congr
  intro choices
  apply FiniteDistribution.expectation_congr
  intro flags
  exact questionStatistic_expectation S hbranch hnode F κ σ r ρ A direction threshold s q choices flags

theorem probability_eq_tag_average (cube : Nat) (hcube : 0 < cube) :
    (CleanDecoderPairLaw.pairLaw S σ (CleanPhysicalDecoderLaw.useful S F κ)
      r ρ A (LinearMap.ker A) (nativeDirection S hnode direction) threshold cube hcube).probability
        (fun z => DecoderRankSplit.highAgrees S hbranch s z.1 z.2) =
      (PreliminarySampler.questionsLaw
        (branch := branch) (n := h + 1) (t := t) (m := m)).expectation
        (fun q => (SourceProjectedTag.law (t := t)
          (fun _ : Fin (branch h) => ProjectedCleanRate.projectionFlag cube hcube)).expectation
          (fun tag => SourceQuestionPhysicalHigh.success
            S.outside S.placeholder S.clauses S.designated q tag.1 tag.2
            upper (suffix S) (suffix_proper S) (h + 1) hbranch d hnode A S.cut σ
            (OriginalDecoderMark.mark F upper (h + 1) κ
              (SourceQuestionPhysicalHigh.originalSlots
                (CleanDecoderRate.path S) S.outside S.clauses q))
            ρ threshold S.exterior direction s)) := by
  simpa only [SourceProjectedTag.law, FiniteDistribution.expectation_product] using
    mean_probability_eq S hbranch hnode F κ σ r ρ A direction threshold s cube hcube

end
end PerfectCompleteness.CleanPhysicalHighAverage

end

end OAI
