import OAI.Computability.PerfectCompleteness.Construction.SourcePhysicalTaggedChildren
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionRawSwap
import OAI.Computability.PerfectCompleteness.Sampling.CandidateCoupling

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalChildExpectation

noncomputable section

open scoped Classical
open RecursiveSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def observe (q : PreliminarySampler.Questions branch (n + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (raw : SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated) :
    Σ flags : SourceProjectedTag.Flags (branch := branch) (n := n),
      CutChildGrouping.Raw (C := C)
        (SourceProjectedTag.mixedInside clauses designated q choices flags) rows :=
  SourcePhysicalTaggedChildren.observe rows clauses designated
    (SourceQuestionKernelJoint.sources designated q choices) raw

@[simp] theorem observe_flags
    (q : PreliminarySampler.Questions branch (n + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (raw : SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated) :
    (observe rows clauses designated q choices raw).1 =
      fun child => SourceChildKernel.rawProjected rows clauses designated child (raw child) := rfl

theorem observe_sample_heq
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated) :
    HEq (observe rows clauses designated
      (SourceQuestionRawSwap.insideQuestions rows clauses designated sample)
      (SourceQuestionRawSwap.positions rows clauses designated sample)
      (SourceQuestionRawSwap.raw rows clauses designated sample))
      (SourcePhysicalTaggedChildren.observe rows clauses designated
        (fun child => ((sample child).1, (sample child).2.1))
        (fun child => (sample child).2.2)) := by
  have congrObserve (sources other : SourceChildKernel.Sources (m := m) (t := t) designated)
      (hs : sources = other)
      (raw : SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated) :
      HEq (SourcePhysicalTaggedChildren.observe rows clauses designated sources raw)
        (SourcePhysicalTaggedChildren.observe rows clauses designated other raw) := by
    cases hs
    rfl
  exact congrObserve _ _
    (SourceQuestionRawSwap.sources_insideQuestions_positions rows clauses designated sample)
    (SourceQuestionRawSwap.raw rows clauses designated sample)

theorem kernel_expectation
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (q : PreliminarySampler.Questions branch (n + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (F : (flags : SourceProjectedTag.Flags (branch := branch) (n := n)) →
      CutChildGrouping.Raw (C := C)
        (SourceProjectedTag.mixedInside clauses designated q choices flags) rows → ℝ) :
    (SourceQuestionRawSwap.kernelLaw (C := C) rows clauses designated flag q choices).expectation
        (fun raw =>
          let observed := observe rows clauses designated q choices raw
          F observed.1 observed.2) =
      (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
        (CutChildGrouping.rawLaw (C := C)
          (SourceProjectedTag.mixedInside clauses designated q choices flags) rows).expectation
            (F flags)) := by
  let statistic :
      (Σ flags : SourceProjectedTag.Flags (branch := branch) (n := n),
        CutChildGrouping.Raw (C := C)
          (SourceProjectedTag.mixedInside clauses designated q choices flags) rows) → ℝ :=
    fun observed => F observed.1 observed.2
  let physical := fun flags : SourceProjectedTag.Flags (branch := branch) (n := n) =>
    CutChildGrouping.rawLaw (C := C)
      (SourceProjectedTag.mixedInside clauses designated q choices flags) rows
  have hlaw :
      (SourceQuestionRawSwap.kernelLaw (C := C) rows clauses designated flag q choices).pushforward
          (observe rows clauses designated q choices) =
        CompletionSoundness.sigmaLaw (SourceProjectedTag.flagLaw flag) physical :=
    SourcePhysicalTaggedChildren.kernels_tagged (C := C) rows clauses designated flag
      (SourceQuestionKernelJoint.sources designated q choices)
  calc
    _ = ((SourceQuestionRawSwap.kernelLaw (C := C) rows clauses designated flag q choices).pushforward
        (observe rows clauses designated q choices)).expectation statistic :=
      (FiniteDistribution.expectation_pushforward
        (SourceQuestionRawSwap.kernelLaw (C := C) rows clauses designated flag q choices)
        (observe rows clauses designated q choices) statistic).symm
    _ = (CompletionSoundness.sigmaLaw (SourceProjectedTag.flagLaw flag) physical).expectation
        statistic := congrArg (fun μ => FiniteDistribution.expectation μ statistic) hlaw
    _ = _ := CandidateCoupling.expectation_sigmaLaw
      (SourceProjectedTag.flagLaw flag) physical statistic

theorem originalLaw_expectation [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (F : (q : PreliminarySampler.Questions branch (n + 1) t m) →
      (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t)) →
      (flags : SourceProjectedTag.Flags (branch := branch) (n := n)) →
      CutChildGrouping.Raw (C := C)
        (SourceProjectedTag.mixedInside clauses designated q choices flags) rows → ℝ) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).expectation
        (fun sample =>
          let q := SourceQuestionRawSwap.insideQuestions rows clauses designated sample
          let choices := SourceQuestionRawSwap.positions rows clauses designated sample
          let observed := observe rows clauses designated q choices
            (SourceQuestionRawSwap.raw rows clauses designated sample)
          F q choices observed.1 observed.2) =
      (PreliminarySampler.questionsLaw
        (branch := branch) (n := n + 1) (t := t) (m := m)).expectation
          (fun q => (SourceProjectedTag.positionLaw
            (branch := branch) (n := n) (t := t)).expectation
              (fun choices => (SourceProjectedTag.flagLaw flag).expectation
                (fun flags => (CutChildGrouping.rawLaw (C := C)
                  (SourceProjectedTag.mixedInside clauses designated q choices flags) rows).expectation
                    (F q choices flags)))) := by
  rw [SourceQuestionRawSwap.originalLaw_expectation rows clauses designated flag
    (fun q choices raw =>
      let observed := observe rows clauses designated q choices raw
      F q choices observed.1 observed.2)]
  apply FiniteDistribution.expectation_congr
  intro q
  apply FiniteDistribution.expectation_congr
  intro choices
  exact kernel_expectation rows clauses designated flag q choices (F q choices)

end
end PerfectCompleteness.SourcePhysicalChildExpectation

end

end OAI
