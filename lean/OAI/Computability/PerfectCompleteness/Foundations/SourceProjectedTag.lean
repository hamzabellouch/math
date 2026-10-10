import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionKernelJoint
import OAI.Computability.PerfectCompleteness.Sampling.WholeArrayHiddenLaw

namespace OAI

section

namespace PerfectCompleteness.SourceProjectedTag

noncomputable section

open scoped Classical
open RecursiveSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t m v : Nat}

abbrev Flags := Fin (branch n) → Bool

abbrev Tag :=
  SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t) ×
    Flags (branch := branch) (n := n)

def positionLaw : FiniteDistribution
    (SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t)) :=
  FiniteProduct.law (fun _ : Fin (branch n) =>
    FiniteDistribution.uniform
      (SourceQuestionPositionSplit.ChildPositions (branch := branch) (n := n) (t := t)))

def flagLaw (flag : Fin (branch n) → FiniteDistribution Bool) :
    FiniteDistribution (Flags (branch := branch) (n := n)) :=
  FiniteProduct.law flag

def law (flag : Fin (branch n) → FiniteDistribution Bool) :
    FiniteDistribution (Tag (branch := branch) (n := n) (t := t)) :=
  (positionLaw (branch := branch) (n := n) (t := t)).product (flagLaw flag)

def sourceFlagEquiv (designated : Fin (branch n) → Slots branch n) :
    (SourceChildKernel.Sources (m := m) (t := t) designated ×
      Flags (branch := branch) (n := n)) ≃
    SourceQuestionPositionSplit.Questions (branch := branch) (n := n) (t := t) (m := m) ×
      Tag (branch := branch) (n := n) (t := t) :=
  (Equiv.prodCongr (SourceQuestionKernelJoint.sourceEquiv designated) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)

@[simp] theorem sourceFlagEquiv_apply (designated : Fin (branch n) → Slots branch n)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
    (flags : Flags (branch := branch) (n := n)) :
    sourceFlagEquiv designated (sources, flags) =
      ((SourceQuestionKernelJoint.sourceEquiv designated sources).1,
        ((SourceQuestionKernelJoint.sourceEquiv designated sources).2, flags)) := rfl

@[simp] theorem sourceFlagEquiv_symm_apply (designated : Fin (branch n) → Slots branch n)
    (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := n) (t := t) (m := m))
    (tag : Tag (branch := branch) (n := n) (t := t)) :
    (sourceFlagEquiv designated).symm (q, tag) =
      (SourceQuestionKernelJoint.sources designated q tag.1, tag.2) := rfl

theorem sourceFlagEquiv_law [NeZero m]
    (designated : Fin (branch n) → Slots branch n)
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    ((SourceChildQuestionLaw.sourceLaw m t designated).product (flagLaw flag)).pushforward
        (sourceFlagEquiv (m := m) (t := t) designated) =
      (PreliminarySampler.questionsLaw
        (branch := branch) (n := n + 1) (t := t) (m := m)).product (law (t := t) flag) := by
  exact WholeArrayHiddenLaw.product_split_first
    (SourceChildQuestionLaw.sourceLaw m t designated) (flagLaw flag)
    (PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m))
    (positionLaw (branch := branch) (n := n) (t := t))
    (SourceQuestionKernelJoint.sourceEquiv designated)
    (SourceQuestionKernelJoint.sourceLaw_sourceEquiv designated)

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)
  (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := n) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
  (flags : Flags (branch := branch) (n := n))

def originalSlots : Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q)

theorem parentLeftSlots_sources :
    SourceChildKernel.parentLeftSlots clauses designated
        (SourceQuestionKernelJoint.sources designated q choices) =
      originalSlots clauses q := by
  rw [SourceQuestionKernelJoint.sources_eq_join,
    SourceQuestionPositionSplit.parentLeftSlots_join]
  rfl

def mixedInside : Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  fun leaf j => SourceChildKernel.mixedSlots clauses designated leaf.1
    (SourceQuestionKernelJoint.sources designated q choices leaf.1) (flags leaf.1) leaf.2 j

def projection : ∀ leaf j, MixedSupport.Projection (originalSlots clauses q leaf j)
    (mixedInside clauses designated q choices flags leaf j) := by
  intro leaf j
  have hslots := congrFun (congrFun (parentLeftSlots_sources clauses designated q choices) leaf) j
  change SourceChildKernel.nativeSlots clauses designated leaf.1
      (SourceQuestionKernelJoint.sources designated q choices leaf.1) leaf.2 j =
    originalSlots clauses q leaf j at hslots
  rw [← hslots]
  exact SourceChildKernel.projection clauses designated leaf.1
    (SourceQuestionKernelJoint.sources designated q choices leaf.1) (flags leaf.1) leaf.2 j

end
end PerfectCompleteness.SourceProjectedTag

end

end OAI
