import OAI.Computability.PerfectCompleteness.Construction.SourceChildKernelLemmas
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionPositionSplit

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionKernelJoint

open scoped Classical
open RecursiveSpaces SourceQuestionPositionSplit
open UniqueGamesTheorem.Foundations.Games

noncomputable section

private theorem kernelJoint_pushforward_first {S T R : Type*}
    [Fintype S] [Fintype T] [Fintype R]
    (μ : FiniteDistribution S) (kernel : S → FiniteDistribution R) (e : S ≃ T) :
    (CleanConditioning.kernelJoint μ kernel).pushforward
        (Equiv.prodCongr e (Equiv.refl R)) =
      CleanConditioning.kernelJoint (μ.pushforward e) (fun s => kernel (e.symm s)) := by
  simp only [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro point
  rfl

variable {branch : Nat → Nat} {n t v m : Nat}

abbrev ChoiceTuple :=
  Fin (branch n) → ChildPositions (branch := branch) (n := n) (t := t)

def sourceEquiv (designated : Fin (branch n) → Slots branch n) :
    SourceChildKernel.Sources (m := m) (t := t) designated ≃
      Questions (branch := branch) (n := n) (t := t) (m := m) ×
        ChoiceTuple (branch := branch) (n := n) (t := t) :=
  (SourceQuestionPositionSplit.split designated).trans
    (Equiv.prodCongr (Equiv.refl _) SourceQuestionPositionSplit.byChild)

def sources (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (choices : ChoiceTuple (branch := branch) (n := n) (t := t)) :
    SourceChildKernel.Sources (m := m) (t := t) designated :=
  (sourceEquiv designated).symm (q, choices)

@[simp] theorem sources_eq_join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (choices : ChoiceTuple (branch := branch) (n := n) (t := t)) :
    sources designated q choices =
      SourceQuestionPositionSplit.join designated q
        (SourceQuestionPositionSplit.byChild.symm choices) := rfl

theorem sourceLaw_sourceEquiv [NeZero m]
    (designated : Fin (branch n) → Slots branch n) :
    (SourceChildQuestionLaw.sourceLaw m t designated).pushforward (sourceEquiv designated) =
      (PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m)).product
        (FiniteProduct.law (fun _ : Fin (branch n) =>
          FiniteDistribution.uniform (ChildPositions (branch := branch) (n := n) (t := t)))) := by
  calc
    _ = ((SourceChildQuestionLaw.sourceLaw m t designated).pushforward
        (SourceQuestionPositionSplit.split designated)).pushforward
          (Equiv.prodCongr (Equiv.refl _) SourceQuestionPositionSplit.byChild) := by
      rw [FiniteDistribution.pushforward_comp]
      rfl
    _ = _ := by
      rw [SourceQuestionPositionSplit.sourceLaw_split]
      change ((PreliminarySampler.questionsLaw
          (branch := branch) (n := n + 1) (t := t) (m := m)).product
          (FiniteDistribution.uniform (Positions (branch := branch) (n := n) (t := t)))).pushforward
        (fun x => (id x.1, SourceQuestionPositionSplit.byChild x.2)) = _
      rw [FiniteDistribution.product_pushforward, FiniteDistribution.pushforward_id,
        SourceQuestionPositionSplit.positions_byChild]

variable {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def groupEquiv :
    SourceChildKernel.Sample (C := C) (t := t) rows clauses designated ≃
      (Questions (branch := branch) (n := n) (t := t) (m := m) ×
        ChoiceTuple (branch := branch) (n := n) (t := t)) ×
          SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated :=
  (SourceChildKernelJoint.groupEquiv rows clauses designated).trans
    (Equiv.prodCongr (sourceEquiv designated) (Equiv.refl _))

@[simp] theorem groupEquiv_raw
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated)
    (i : Fin (branch n)) :
    (groupEquiv rows clauses designated sample).2 i = (sample i).2.2 := rfl

theorem originalLaw_group [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (groupEquiv rows clauses designated) =
      CleanConditioning.kernelJoint
        ((PreliminarySampler.questionsLaw
          (branch := branch) (n := n + 1) (t := t) (m := m)).product
            (FiniteProduct.law (fun _ : Fin (branch n) =>
              FiniteDistribution.uniform
                (ChildPositions (branch := branch) (n := n) (t := t)))))
        (fun qp => FiniteProduct.law (fun i =>
          SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i
            (sources designated qp.1 qp.2 i))) := by
  calc
    _ = ((SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (SourceChildKernelJoint.groupEquiv rows clauses designated)).pushforward
          (Equiv.prodCongr (sourceEquiv designated) (Equiv.refl _)) := by
      rw [FiniteDistribution.pushforward_comp]
      rfl
    _ = (CleanConditioning.kernelJoint (SourceChildQuestionLaw.sourceLaw m t designated)
        (fun source => FiniteProduct.law (fun i =>
          SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i
            (source i)))).pushforward
          (Equiv.prodCongr (sourceEquiv designated) (Equiv.refl _)) := by
      rw [SourceChildKernelJoint.originalLaw_group]
      rfl
    _ = _ := by
      rw [kernelJoint_pushforward_first, sourceLaw_sourceEquiv]
      rfl

end
end PerfectCompleteness.SourceQuestionKernelJoint

end

end OAI
