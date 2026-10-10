import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedExperiment

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedArrays

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

private theorem mpr_heq {α β : Sort _} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

private theorem sourceProjection_heq
    {branch : Nat → Nat} {i t v m : Nat}
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch i) → Slots branch i)
    (q : PreliminarySampler.Questions branch (i + 1) t m)
    (positions : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i))
    (leaf : Slots branch (i + 1)) (a : Fin t) :
    HEq (SourceProjectedTag.projection clauses designated q positions flags leaf a)
      (SourceChildKernel.projection clauses designated leaf.1
        (SourceQuestionKernelJoint.sources designated q positions leaf.1)
        (flags leaf.1) leaf.2 a) := by
  unfold SourceProjectedTag.projection
  dsimp only [id]
  exact mpr_heq _ _

private theorem fillProjection_heq
    {branch : Nat → Nat} {n h t : Nat} (p : Path branch n h)
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    {left left' right right' : Slots branch h → Fin t → MixedSupport.Slot}
    (hl : left = left') (hr : right = right')
    (q : ∀ s a, MixedSupport.Projection (left s a) (right s a))
    (q' : ∀ s a, MixedSupport.Projection (left' s a) (right' s a))
    (hq : ∀ s a, HEq (q s a) (q' s a)) (leaf : Slots branch n) (a : Fin t) :
    HEq (CutProjectionAssembly.fillProjection p outside left right q leaf a)
      (CutProjectionAssembly.fillProjection p outside left' right' q' leaf a) := by
  cases hl
  cases hr
  have he : q = q' := funext (fun s => funext (fun a => eq_of_heq (hq s a)))
  cases he
  rfl

private theorem arraysPullback_heq
    {branch : Nat → Nat} {n t : Nat} (rows : Nat → Nat)
    {left left' right : Slots branch n → Fin t → MixedSupport.Slot}
    (hl : left = left')
    (q : ∀ s a, MixedSupport.Projection (left s a) (right s a))
    (q' : ∀ s a, MixedSupport.Projection (left' s a) (right s a))
    (hq : ∀ s a, HEq (q s a) (q' s a)) (arrays : Arrays right rows) :
    HEq (ChildBlockProjection.arraysPullback rows q arrays)
      (ChildBlockProjection.arraysPullback rows q' arrays) := by
  cases hl
  have he : q = q' := funext (fun s => funext (fun a => eq_of_heq (hq s a)))
  cases he
  rfl

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

theorem nativeSlots_eq
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : StoppedProjectedExperiment.PhysicalBase
      (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    SourcePhysicalTapeLaw.nativeSlots
        (StoppedProjectedExperiment.stoppedPath rows hupper hij o
          (StoppedProjectedExperiment.baseTag rows base))
        (StoppedProjectedExperiment.nativeSlots clauses o) clauses designated
        (StoppedProjectedExperiment.physicalSources rows hupper hij designated o base) =
      StoppedProjectedExperiment.nativeSlots clauses o := by
  unfold SourcePhysicalTapeLaw.nativeSlots StoppedProjectedExperiment.physicalSources
  rw [SourceProjectedTag.parentLeftSlots_sources]
  exact StoppedProjectedExperiment.fill_native clauses rows hupper hij o
    (StoppedProjectedExperiment.baseTag rows base)

theorem projection_heq
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : StoppedProjectedExperiment.PhysicalBase
      (branch := branch) (n := n) (i := i) (j := j) (t := t) rows)
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i))
    (leaf : Slots branch n) (a : Fin t) :
    HEq (StoppedProjectedExperiment.projection clauses rows hupper hij designated o
        (StoppedProjectedExperiment.withFlags rows base flags) leaf a)
      (SourcePhysicalTapeLaw.fullProjection
        (StoppedProjectedExperiment.stoppedPath rows hupper hij o
          (StoppedProjectedExperiment.baseTag rows base))
        (StoppedProjectedExperiment.nativeSlots clauses o) clauses designated
        (StoppedProjectedExperiment.physicalSources rows hupper hij designated o base, flags)
        leaf a) := by
  unfold StoppedProjectedExperiment.projection
  apply (CutProjectionAssembly.castProjection_heq _ _ _).trans
  exact fillProjection_heq
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedExperiment.baseTag rows base))
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (SourceProjectedTag.parentLeftSlots_sources clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows base)) base.2.1).symm
    rfl _ _
    (sourceProjection_heq clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows base)) base.2.1 flags) leaf a

abbrev physicalArrays
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.PhysicalSample
      clauses rows repeats hupper hij designated o) :=
  SourcePhysicalWholeLaw.observeLeft rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedExperiment.baseTag rows sample.1))
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows sample.1)))
    clauses designated
    (StoppedProjectedExperiment.physicalSources rows hupper hij designated o sample.1) sample.2

variable [NeZero m]
  (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

omit [NeZero m] in
theorem arrays_physicalExperimentRead_heq
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.PhysicalSample
      clauses rows repeats hupper hij designated o) :
    HEq ((StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
        hbranch hrows flag σ o).arrays
      (StoppedProjectedExperiment.physicalExperimentRead clauses rows repeats hupper hij designated
        o sample))
      (physicalArrays clauses rows repeats hupper hij designated o sample) := by
  let observed := SourcePhysicalTapeLaw.observeFiber rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedExperiment.baseTag rows sample.1))
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows sample.1)))
    clauses designated
    (StoppedProjectedExperiment.physicalSources rows hupper hij designated o sample.1) sample.2
  have htable := StoppedProjectedExperiment.arrays_tapeRead clauses rows repeats hupper hij
    designated hbranch hrows flag σ o
    (StoppedProjectedExperiment.physicalRead clauses rows repeats hupper hij designated o sample)
  have hpull := arraysPullback_heq rows
    (nativeSlots_eq clauses rows hupper hij designated o sample.1).symm
    (StoppedProjectedExperiment.projection clauses rows hupper hij designated o
      (StoppedProjectedExperiment.withFlags rows sample.1 observed.1))
    (SourcePhysicalTapeLaw.fullProjection
      (StoppedProjectedExperiment.stoppedPath rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows sample.1))
      (StoppedProjectedExperiment.nativeSlots clauses o) clauses designated
      (StoppedProjectedExperiment.physicalSources rows hupper hij designated o sample.1, observed.1))
    (projection_heq clauses rows hupper hij designated o sample.1 observed.1)
    (WholeArraySampler.evaluate rows repeats
      (StoppedProjectedExperiment.stoppedPath rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows sample.1))
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
        (StoppedProjectedExperiment.withFlags rows sample.1 observed.1)) observed.2)
  have hphysical := SourcePhysicalTapeLaw.observeFiber_native_arrays rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedExperiment.baseTag rows sample.1))
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows sample.1)))
    clauses designated
    (StoppedProjectedExperiment.physicalSources rows hupper hij designated o sample.1) sample.2
  exact (heq_of_eq htable).trans (hpull.trans (heq_of_eq hphysical))

omit [NeZero m] in
theorem arrays_physicalExperimentRead_eq
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.PhysicalSample
      clauses rows repeats hupper hij designated o) :
    (StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
        hbranch hrows flag σ o).arrays
      (StoppedProjectedExperiment.physicalExperimentRead clauses rows repeats hupper hij designated
        o sample) =
      cast (congrArg
        (fun slots : Slots branch n → Fin t → MixedSupport.Slot => Arrays slots rows)
        (nativeSlots_eq clauses rows hupper hij designated o sample.1))
        (physicalArrays clauses rows repeats hupper hij designated o sample) := by
  apply eq_of_heq
  exact (arrays_physicalExperimentRead_heq clauses rows repeats hupper hij designated
    hbranch hrows flag σ o sample).trans (cast_heq _ _).symm

end
end PerfectCompleteness.StoppedProjectedArrays

end

end OAI
