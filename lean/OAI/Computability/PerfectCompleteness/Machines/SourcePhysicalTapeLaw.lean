import OAI.Computability.PerfectCompleteness.Construction.SourceChildKernelLemmas
import OAI.Computability.PerfectCompleteness.Construction.SourcePhysicalTaggedChildren
import OAI.Computability.PerfectCompleteness.Machines.SourcePhysicalTapeFiber
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalCanonicalQuery
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildQuestionLaw
import OAI.Computability.PerfectCompleteness.Sampling.SourcePhysicalWholeLaw
import OAI.Computability.PerfectCompleteness.Sampling.TaggedKernelRebuildLaw

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalTapeLaw

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Tag := SourceChildKernel.Sources (m := m) (t := t) designated ×
  (Fin (branch h) → Bool)

def insideSlots (tag : Tag (m := m) (t := t) designated) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  SourcePhysicalTaggedChildren.slots clauses designated tag.1 tag.2

def nativeSlots (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    Slots branch root → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources)

def projectedSlots (tag : Tag (m := m) (t := t) designated) :
    Slots branch root → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill p outside (insideSlots clauses designated tag)

def fullProjection (tag : Tag (m := m) (t := t) designated) :
    ∀ s k, MixedSupport.Projection
      (nativeSlots p outside clauses designated tag.1 s k)
      (projectedSlots p outside clauses designated tag s k) :=
  CutProjectionAssembly.fillProjection p outside _ _
    (fun leaf k => SourceChildKernel.projection clauses designated leaf.1
      (tag.1 leaf.1) (tag.2 leaf.1) leaf.2 k)

abbrev Sample := CleanPhysicalReplay.Sample (t := t) rows repeats p clauses designated

abbrev Exterior := CleanPhysicalReplay.Exterior rows repeats p outside placeholder

abbrev Record := Σ tag : Tag (m := m) (t := t) designated,
  WholeArraySampler.Tape rows repeats p (projectedSlots p outside clauses designated tag)

def rebuild (tag : Tag (m := m) (t := t) designated)
    (external : Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (insideSlots clauses designated tag) rows) :
    WholeArraySampler.Tape rows repeats p (projectedSlots p outside clauses designated tag) :=
  WholeCutSampler.collapse rows repeats p (projectedSlots p outside clauses designated tag)
    (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder
      (insideSlots clauses designated tag) external children)

def sourceTag (sample : Sample (t := t) rows repeats p clauses designated) :
    SourceChildKernel.Sources (m := m) (t := t) designated :=
  (SourceChildKernelJoint.groupEquiv rows clauses designated sample).1

def tag (sample : Sample (t := t) rows repeats p clauses designated) :
    Tag (m := m) (t := t) designated :=
  (sourceTag rows repeats p clauses designated sample,
    fun i => SourceChildKernel.rawProjected rows clauses designated i (sample i).2.2)

def observe
    (sample : Sample (t := t) rows repeats p clauses designated ×
      Exterior rows repeats p outside placeholder) :
    Record rows repeats p outside clauses designated :=
  ⟨tag rows repeats p clauses designated sample.1,
    rebuild rows repeats p outside placeholder clauses designated
      (tag rows repeats p clauses designated sample.1) sample.2
      (SourceChildKernel.rightChildren rows clauses designated
        (sourceTag rows repeats p clauses designated sample.1) (fun i => (sample.1 i).2.2))⟩

def observeFiber (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
    (sample : SourcePhysicalWholeLaw.Raw rows repeats p outside placeholder clauses designated) :
    Σ flags : Fin (branch h) → Bool,
      WholeArraySampler.Tape rows repeats p
        (projectedSlots p outside clauses designated (sources, flags)) :=
  let decoded := SourcePhysicalTaggedChildren.observe rows clauses designated sources sample.2
  ⟨decoded.1, rebuild rows repeats p outside placeholder clauses designated
    (sources, decoded.1) sample.1 decoded.2⟩

omit [NeZero m] in
theorem rebuild_law (tag : Tag (m := m) (t := t) designated) :
    ((FiniteDistribution.uniform (Exterior rows repeats p outside placeholder)).product
      (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p)
        (insideSlots clauses designated tag) rows)).pushforward
          (fun x => rebuild rows repeats p outside placeholder clauses designated tag x.1 x.2) =
      WholeArraySampler.tapeLaw rows repeats p (projectedSlots p outside clauses designated tag) :=
  SourcePhysicalTapeFiber.collapse_physicalTape_law rows repeats p outside placeholder
    (insideSlots clauses designated tag)

omit [NeZero m] in
theorem observeFiber_law (flag : Fin (branch h) → FiniteDistribution Bool)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    (SourcePhysicalWholeLaw.rawLaw rows repeats p outside placeholder clauses designated
      flag sources).pushforward
        (observeFiber rows repeats p outside placeholder clauses designated sources) =
      CompletionSoundness.sigmaLaw (FiniteProduct.law flag) (fun flags =>
        WholeArraySampler.tapeLaw rows repeats p
          (projectedSlots p outside clauses designated (sources, flags))) := by
  exact TaggedKernelRebuildLaw.fiber_rebuild_law
    (FiniteProduct.law flag)
    (FiniteDistribution.uniform (Exterior rows repeats p outside placeholder))
    (FiniteProduct.law (fun i => SourceChildKernel.kernel
      (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated flag i (sources i)))
    (fun flags => CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p)
      (insideSlots clauses designated (sources, flags)) rows)
    (fun flags => WholeArraySampler.tapeLaw rows repeats p
      (projectedSlots p outside clauses designated (sources, flags)))
    (SourcePhysicalTaggedChildren.observe rows clauses designated sources)
    (fun flags => rebuild rows repeats p outside placeholder clauses designated (sources, flags))
    (SourcePhysicalTaggedChildren.kernels_tagged rows clauses designated flag sources)
    (fun flags => rebuild_law rows repeats p outside placeholder clauses designated (sources, flags))

def law (flag : Fin (branch h) → FiniteDistribution Bool) :
    FiniteDistribution (Sample (t := t) rows repeats p clauses designated ×
      Exterior rows repeats p outside placeholder) :=
  (SourceChildKernel.originalLaw (C := WholeCutCalls.Index rows repeats p)
    (t := t) rows clauses designated flag).product
      (FiniteDistribution.uniform (Exterior rows repeats p outside placeholder))

def tagLaw (flag : Fin (branch h) → FiniteDistribution Bool) :
    FiniteDistribution (Tag (m := m) (t := t) designated) :=
  (SourceChildQuestionLaw.sourceLaw m t designated).product (FiniteProduct.law flag)

theorem observe_law (flag : Fin (branch h) → FiniteDistribution Bool) :
    (law rows repeats p outside placeholder clauses designated flag).pushforward
        (observe rows repeats p outside placeholder clauses designated) =
      CompletionSoundness.sigmaLaw (tagLaw (m := m) (t := t) designated flag) (fun tag =>
        WholeArraySampler.tapeLaw rows repeats p (projectedSlots p outside clauses designated tag)) := by
  let group := fun sample : Sample (t := t) rows repeats p clauses designated ×
      Exterior rows repeats p outside placeholder =>
    (SourceChildKernelJoint.groupEquiv rows clauses designated sample.1, sample.2)
  let decode := SourcePhysicalTaggedChildren.observe
    (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated
  let rebuildTag := fun sample :
      (SourceChildKernel.Sources (m := m) (t := t) designated ×
        SourceChildKernelJoint.RawTuple (C := WholeCutCalls.Index rows repeats p)
          (t := t) rows clauses designated) × Exterior rows repeats p outside placeholder =>
    (⟨(sample.1.1, (decode sample.1.1 sample.1.2).1),
      rebuild rows repeats p outside placeholder clauses designated
        (sample.1.1, (decode sample.1.1 sample.1.2).1) sample.2
        (decode sample.1.1 sample.1.2).2⟩ : Record rows repeats p outside clauses designated)
  have hgroup : (law rows repeats p outside placeholder clauses designated flag).pushforward group =
      (CleanConditioning.kernelJoint (SourceChildQuestionLaw.sourceLaw m t designated)
        (fun sources => FiniteProduct.law (fun i => SourceChildKernel.kernel
          (C := WholeCutCalls.Index rows repeats p) (t := t)
          rows clauses designated flag i (sources i)))).product
            (FiniteDistribution.uniform (Exterior rows repeats p outside placeholder)) := by
    change ((SourceChildKernel.originalLaw (C := WholeCutCalls.Index rows repeats p)
      (t := t) rows clauses designated flag).product
        (FiniteDistribution.uniform (Exterior rows repeats p outside placeholder))).pushforward
          (fun x => (SourceChildKernelJoint.groupEquiv rows clauses designated x.1, id x.2)) = _
    rw [FiniteDistribution.product_pushforward, SourceChildKernelJoint.originalLaw_group,
      FiniteDistribution.pushforward_id, SourceChildQuestionLaw.sourceLaw]
  calc
    _ = ((law rows repeats p outside placeholder clauses designated flag).pushforward group).pushforward
        rebuildTag := by
      rw [FiniteDistribution.pushforward_comp]
      rfl
    _ = _ := by
      rw [hgroup]
      exact TaggedKernelRebuildLaw.rebuild_law
        (SourceChildQuestionLaw.sourceLaw m t designated) (FiniteProduct.law flag)
        (FiniteDistribution.uniform (Exterior rows repeats p outside placeholder))
        (fun sources => FiniteProduct.law (fun i => SourceChildKernel.kernel
          (C := WholeCutCalls.Index rows repeats p) (t := t)
          rows clauses designated flag i (sources i)))
        (fun sources flags => CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p)
          (insideSlots clauses designated (sources, flags)) rows)
        (fun sources flags => WholeArraySampler.tapeLaw rows repeats p
          (projectedSlots p outside clauses designated (sources, flags))) decode
        (fun sources flags => rebuild rows repeats p outside placeholder clauses designated (sources, flags))
        (fun sources => SourcePhysicalTaggedChildren.kernels_tagged rows clauses designated flag sources)
        (fun sources flags => rebuild_law rows repeats p outside placeholder clauses designated (sources, flags))

omit [NeZero m] in
theorem observe_tape
    (sample : Sample (t := t) rows repeats p clauses designated ×
      Exterior rows repeats p outside placeholder) :
    (observe rows repeats p outside placeholder clauses designated sample).2 =
      WholeCutSampler.collapse rows repeats p
        (CutSlotAssembly.fill p outside
          (CleanPhysicalReplay.rightInside rows repeats p clauses designated sample.1))
        (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated
          sample.1 sample.2) := rfl

omit [NeZero m] in
theorem observe_native_arrays
    (sample : Sample (t := t) rows repeats p clauses designated ×
      Exterior rows repeats p outside placeholder) :
    ChildBlockProjection.arraysPullback rows
        (fullProjection p outside clauses designated (tag rows repeats p clauses designated sample.1))
        (WholeArraySampler.evaluate rows repeats p
          (projectedSlots p outside clauses designated (tag rows repeats p clauses designated sample.1))
          (observe rows repeats p outside placeholder clauses designated sample).2) =
      CleanPhysicalCanonicalQuery.leftArrays rows repeats p outside placeholder clauses designated
        sample.1 sample.2 :=
  (CleanPhysicalCanonicalQuery.arrays_pullback rows repeats p outside placeholder clauses designated
    sample.1 sample.2).symm

omit [NeZero m] in
theorem observeFiber_native_arrays
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
    (sample : SourcePhysicalWholeLaw.Raw rows repeats p outside placeholder clauses designated) :
    ChildBlockProjection.arraysPullback rows
        (fullProjection p outside clauses designated
          (sources, (observeFiber rows repeats p outside placeholder clauses designated sources sample).1))
        (WholeArraySampler.evaluate rows repeats p
          (projectedSlots p outside clauses designated
            (sources, (observeFiber rows repeats p outside placeholder clauses designated sources sample).1))
          (observeFiber rows repeats p outside placeholder clauses designated sources sample).2) =
      SourcePhysicalWholeLaw.observeLeft rows repeats p outside placeholder clauses designated sources sample :=
  (WholeCutGroupedProjection.physicalTape_pullback rows repeats p outside placeholder
    (SourceChildKernel.parentLeftSlots clauses designated sources)
    (SourceChildKernel.parentRightSlots rows clauses designated sources sample.2)
    (SourceChildKernel.parentProjection rows clauses designated sources sample.2) sample.1
    (SourceChildKernel.rightChildren rows clauses designated sources sample.2)).symm

end
end PerfectCompleteness.SourcePhysicalTapeLaw

end

end OAI
