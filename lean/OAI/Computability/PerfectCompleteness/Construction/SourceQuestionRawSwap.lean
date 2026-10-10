import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionCutSplit
import OAI.Computability.PerfectCompleteness.Foundations.SourceProjectedTag

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionRawSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games

private theorem expectation_kernelJoint {S R : Type*} [Fintype S] [Fintype R]
    (μ : FiniteDistribution S) (P : S → FiniteDistribution R) (f : S × R → ℝ) :
    (CleanConditioning.kernelJoint μ P).expectation f =
      μ.expectation (fun s => (P s).expectation (fun r => f (s, r))) := by
  simp only [FiniteDistribution.expectation, CleanConditioning.kernelJoint,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

variable {branch : Nat → Nat} {root h n t v m : Nat}

@[simp] theorem restrict_join (p : Path branch root h)
    (inside : PreliminarySampler.Questions branch h t m)
    (external : SourceQuestionCutSplit.OutsideQuestions p t m) :
    SourceQuestionCutSplit.restrict p (SourceQuestionCutSplit.join p inside external) =
      inside := by
  funext leaf
  exact SourceQuestionCutSplit.join_at_cut p inside external leaf

theorem questions_expectation [NeZero m] (p : Path branch root h)
    (F : PreliminarySampler.Questions branch root t m → ℝ) :
    (PreliminarySampler.questionsLaw
        (branch := branch) (n := root) (t := t) (m := m)).expectation F =
      (FiniteDistribution.uniform (SourceQuestionCutSplit.OutsideQuestions p t m)).expectation
        (fun external => (PreliminarySampler.questionsLaw
          (branch := branch) (n := h) (t := t) (m := m)).expectation
            (fun inside => F (SourceQuestionCutSplit.join p inside external))) := by
  have hsplit := congrArg (fun μ : FiniteDistribution
      (PreliminarySampler.Questions branch h t m ×
        SourceQuestionCutSplit.OutsideQuestions p t m) =>
      μ.expectation (fun parts => F ((SourceQuestionCutSplit.splitEquiv p).symm parts)))
    (SourceQuestionCutSplit.split_law (t := t) (m := m) p)
  rw [FiniteDistribution.expectation_pushforward,
    FiniteDistribution.expectation_product] at hsplit
  simp only [Equiv.symm_apply_apply] at hsplit
  exact hsplit.trans (FiniteDistribution.expectation_comm
    (PreliminarySampler.questionsLaw (branch := branch) (n := h) (t := t) (m := m))
    (FiniteDistribution.uniform (SourceQuestionCutSplit.OutsideQuestions p t m))
    (fun inside external => F (SourceQuestionCutSplit.join p inside external)))

variable {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def insideQuestions
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated) :
    PreliminarySampler.Questions branch (n + 1) t m :=
  (SourceQuestionKernelJoint.groupEquiv rows clauses designated sample).1.1

def positions
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated) :
    SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t) :=
  (SourceQuestionKernelJoint.groupEquiv rows clauses designated sample).1.2

def raw
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated) :
    SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated :=
  (SourceQuestionKernelJoint.groupEquiv rows clauses designated sample).2

@[simp] theorem raw_apply
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated)
    (child : Fin (branch n)) :
    raw rows clauses designated sample child = (sample child).2.2 := rfl

theorem sources_insideQuestions_positions
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated) :
    SourceQuestionKernelJoint.sources designated
        (insideQuestions rows clauses designated sample)
        (positions rows clauses designated sample) =
      fun child => ((sample child).1, (sample child).2.1) := by
  change (SourceQuestionKernelJoint.sourceEquiv designated).symm
      ((SourceQuestionKernelJoint.sourceEquiv designated)
        (fun child => ((sample child).1, (sample child).2.1))) = _
  exact (SourceQuestionKernelJoint.sourceEquiv designated).symm_apply_apply _

def kernelLaw (flag : Fin (branch n) → FiniteDistribution Bool)
    (inside : PreliminarySampler.Questions branch (n + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t)) :
    FiniteDistribution (SourceChildKernelJoint.RawTuple (C := C) (t := t)
      rows clauses designated) :=
  FiniteProduct.law (fun child =>
    SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag child
      (SourceQuestionKernelJoint.sources designated inside choices child))

theorem originalLaw_expectation [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (F : PreliminarySampler.Questions branch (n + 1) t m →
      SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t) →
        SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated → ℝ) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).expectation
        (fun sample => F (insideQuestions rows clauses designated sample)
          (positions rows clauses designated sample) (raw rows clauses designated sample)) =
      (PreliminarySampler.questionsLaw
        (branch := branch) (n := n + 1) (t := t) (m := m)).expectation
          (fun inside => (SourceProjectedTag.positionLaw
            (branch := branch) (n := n) (t := t)).expectation
              (fun choices => (kernelLaw rows clauses designated flag inside choices).expectation
                (F inside choices))) := by
  let statistic : (PreliminarySampler.Questions branch (n + 1) t m ×
      SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t)) ×
      SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated → ℝ :=
    fun grouped => F grouped.1.1 grouped.1.2 grouped.2
  have hgroup := congrArg (fun μ : FiniteDistribution
      ((PreliminarySampler.Questions branch (n + 1) t m ×
        SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t)) ×
        SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated) =>
      μ.expectation statistic)
    (SourceQuestionKernelJoint.originalLaw_group (C := C) (t := t)
      rows clauses designated flag)
  simpa only [FiniteDistribution.expectation_pushforward, expectation_kernelJoint,
    FiniteDistribution.expectation_product, statistic, insideQuestions, positions, raw,
    kernelLaw, SourceProjectedTag.positionLaw] using hgroup

theorem fullQuestions_expectation [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (p : Path branch root (n + 1))
    (F : PreliminarySampler.Questions branch root t m →
      SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t) →
        SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated → ℝ) :
    (PreliminarySampler.questionsLaw
        (branch := branch) (n := root) (t := t) (m := m)).expectation
      (fun q => (SourceProjectedTag.positionLaw
        (branch := branch) (n := n) (t := t)).expectation
          (fun choices => (kernelLaw rows clauses designated flag
            (SourceQuestionCutSplit.restrict p q) choices).expectation
              (fun sampleRaw => F q choices sampleRaw))) =
      (FiniteDistribution.uniform (SourceQuestionCutSplit.OutsideQuestions p t m)).expectation
        (fun external => (SourceChildKernel.originalLaw (C := C) (t := t)
          rows clauses designated flag).expectation
            (fun sample => F
              (SourceQuestionCutSplit.join p
                (insideQuestions rows clauses designated sample) external)
              (positions rows clauses designated sample) (raw rows clauses designated sample))) := by
  rw [questions_expectation p]
  apply FiniteDistribution.expectation_congr
  intro external
  simp only [restrict_join]
  exact (originalLaw_expectation rows clauses designated flag
    (fun inside choices sampleRaw =>
      F (SourceQuestionCutSplit.join p inside external) choices sampleRaw)).symm

end
end PerfectCompleteness.SourceQuestionRawSwap

end

end OAI
