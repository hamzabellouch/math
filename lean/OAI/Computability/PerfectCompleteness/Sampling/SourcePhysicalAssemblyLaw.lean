import OAI.Computability.PerfectCompleteness.Construction.SourceChildKernelLemmas
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildKernelMarginalLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildQuestionLaw

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalAssemblyLaw

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces SourceChildKernel
open scoped Classical

noncomputable section

private theorem kernelJoint_pushforward_sigma {S R : Type*} {Y : S → Type*}
    [Fintype S] [Fintype R] [∀ s, Fintype (Y s)]
    (μ : FiniteDistribution S) (P : S → FiniteDistribution R)
    (f : (s : S) → R → Y s) :
    (CleanConditioning.kernelJoint μ P).pushforward
        (fun x => (⟨x.1, f x.1 x.2⟩ : Σ s, Y s)) =
      CompletionSoundness.sigmaLaw μ (fun s => (P s).pushforward (f s)) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, CleanConditioning.probability_kernelJoint,
    CompletionSoundness.sigmaLaw_probability]
  simp only [FiniteDistribution.expectation, FiniteDistribution.probability_pushforward]

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def assembleLeft (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    CutChildGrouping.Assembled (C := C) (parentLeftSlots clauses designated sources) rows :=
  CutChildGrouping.assemble (parentLeftSlots clauses designated sources) rows
    (leftChildren rows clauses designated sources raw)

theorem assembleLeft_eq_sourcePullback
    (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    assembleLeft rows clauses designated sources raw =
      ChildAssemblyProjection.assembledPullback rows
        (parentProjection rows clauses designated sources raw)
        (CutChildGrouping.assemble (parentRightSlots rows clauses designated sources raw) rows
          (rightChildren rows clauses designated sources raw)) :=
  SourceChildKernel.assemble_leftChildren rows clauses designated sources raw

theorem kernels_assembleLeft (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i =>
      kernel (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
        (assembleLeft rows clauses designated sources) =
      (FiniteProduct.law (fun i =>
        SourceChildNativeLaw.leftLaw (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
          (CutChildGrouping.assemble (C := C) (parentLeftSlots clauses designated sources) rows) := by
  unfold assembleLeft
  rw [← FiniteDistribution.pushforward_comp
    (FiniteProduct.law (fun i =>
      kernel (C := C) (t := t) rows clauses designated flag i (sources i)))
    (leftChildren rows clauses designated sources)
    (CutChildGrouping.assemble (C := C) (parentLeftSlots clauses designated sources) rows),
    SourceChildNativeLaw.kernels_leftChildren]
  rfl

theorem kernels_assembleLeft_false
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i =>
      kernel (C := C) (t := t) rows clauses designated
        (fun _ => SourceChildNativeLaw.falseFlag) i (sources i))).pushforward
          (assembleLeft rows clauses designated sources) =
      FiniteDistribution.uniform
        (CutChildGrouping.Assembled (C := C) (parentLeftSlots clauses designated sources) rows) := by
  unfold assembleLeft
  rw [← FiniteDistribution.pushforward_comp
    (FiniteProduct.law (fun i =>
      kernel (C := C) (t := t) rows clauses designated
        (fun _ => SourceChildNativeLaw.falseFlag) i (sources i)))
    (leftChildren rows clauses designated sources)
    (CutChildGrouping.assemble (C := C) (parentLeftSlots clauses designated sources) rows),
    SourceChildNativeLaw.kernels_leftChildren_false]
  exact CutChildGrouping.assemble_law (C := C) (parentLeftSlots clauses designated sources) rows

abbrev Observation :=
  Σ sources : Sources (m := m) (t := t) designated,
    CutChildGrouping.Assembled (C := C) (parentLeftSlots clauses designated sources) rows

def observe (sample : Sample (C := C) (t := t) rows clauses designated) :
    Observation (C := C) (t := t) rows clauses designated :=
  ⟨(SourceChildKernelJoint.groupEquiv rows clauses designated sample).1,
    assembleLeft rows clauses designated
      (SourceChildKernelJoint.groupEquiv rows clauses designated sample).1
      (SourceChildKernelJoint.groupEquiv rows clauses designated sample).2⟩

private theorem original_observe_kernel_law [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (observe rows clauses designated) =
      CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated)
        (fun sources =>
          (FiniteProduct.law (fun i =>
            kernel (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
              (assembleLeft rows clauses designated sources)) := by
  unfold observe
  rw [← FiniteDistribution.pushforward_comp
    (originalLaw (C := C) (t := t) rows clauses designated flag)
    (SourceChildKernelJoint.groupEquiv rows clauses designated)
    (fun x => (⟨x.1, assembleLeft rows clauses designated x.1 x.2⟩ :
      Observation (C := C) (t := t) rows clauses designated)),
    SourceChildKernelJoint.originalLaw_group]
  exact kernelJoint_pushforward_sigma (SourceChildQuestionLaw.sourceLaw m t designated)
    (fun sources => FiniteProduct.law (fun i =>
      kernel (C := C) (t := t) rows clauses designated flag i (sources i)))
    (assembleLeft rows clauses designated)

theorem original_assembleLeft_law [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (observe rows clauses designated) =
      CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated)
        (fun sources =>
          (FiniteProduct.law (fun i => SourceChildNativeLaw.leftLaw (C := C) (t := t)
            rows clauses designated flag i (sources i))).pushforward
              (CutChildGrouping.assemble (C := C) (parentLeftSlots clauses designated sources) rows)) := by
  rw [original_observe_kernel_law]
  exact congrArg (CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated))
    (funext fun sources => kernels_assembleLeft rows clauses designated flag sources)

theorem original_assembleLeft_false_law [NeZero m] :
    (originalLaw (C := C) (t := t) rows clauses designated
      (fun _ => SourceChildNativeLaw.falseFlag)).pushforward
        (observe rows clauses designated) =
      CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated)
        (fun sources => FiniteDistribution.uniform
          (CutChildGrouping.Assembled (C := C) (parentLeftSlots clauses designated sources) rows)) := by
  rw [original_observe_kernel_law]
  exact congrArg (CompletionSoundness.sigmaLaw (SourceChildQuestionLaw.sourceLaw m t designated))
    (funext fun sources => kernels_assembleLeft_false (C := C) rows clauses designated sources)

end
end PerfectCompleteness.SourcePhysicalAssemblyLaw

end

end OAI
