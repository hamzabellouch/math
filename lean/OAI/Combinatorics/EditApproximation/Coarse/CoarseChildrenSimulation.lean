import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryGrid

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Child arrays are reused exactly as in the shared rational evaluator.
This composition lemma isolates the inductive recursive-call hypothesis. -/
 theorem coarseBinaryChildren_rep {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L : ℕ) (frame : List (Option α)) (two allowance : BinaryFraction)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (htwo : two.value = 2) (ha : allowance.representation.den = two.representation.den)
    (ht : ∀ draw : Fin B,
      (coarseChildThresholdWithWork B q allowance draw).1.value =
        coarseChildThreshold B q allowance.value draw)
    (hs : (coarseChildAllowanceWithWork q allowance).1.value = allowance.value / q)
    (he : ∀ child draw below, (child, draw, below) ∈ children → ∀ start,
      CoarseArrayRep (coarseBinaryEval k q L frame two child below
        (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance draw).1).1 start).1
        (coarseArrayEval k q (1 / L) frame child below
          ((1 / L) * coarseChildThreshold B q allowance.value draw) start).1)
    (start : ℕ) :
    CoarseArrayRep (coarseBinaryChildren k q L two
      (fun child => coarseBinaryEval k q L frame two child) allowance children start).1
      (coarseArrayEvalChildren k q (1 / L) (fun child => coarseArrayEval k q (1 / L) frame child)
        allowance.value children start).1 := by
  induction children generalizing start with
  | nil => rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    let threshold := coarseChildThresholdWithWork B q allowance draw
    let childAllowance := coarseChildAllowanceWithWork L threshold.1
    let evaluated := coarseBinaryEval k q L frame two child below childAllowance.1 start
    let ratEvaluated := coarseArrayEval k q (1 / L) frame child below
      ((1 / L) * coarseChildThreshold B q allowance.value draw) start
    have hthreshold : threshold.1.representation.den = two.representation.den :=
      (coarseChildThresholdWithWork_den B q allowance draw).trans ha
    have hchild : childAllowance.1.representation.den = two.representation.den :=
      (coarseChildAllowanceWithWork_den L threshold.1).trans hthreshold
    have hev : CoarseArrayRep evaluated.1 ratEvaluated.1 := he child draw below List.mem_cons_self start
    have hg : CoarseArrayOnGrid two.representation.den evaluated.1 :=
      coarseBinaryEval_grid k q L frame two child below childAllowance.1 start hchild
    have hp := coarseBinaryPenalty_rep two evaluated.1 ratEvaluated.1 htwo hev hg
    have hpg := coarseBinaryPenalty_grid two evaluated.1 hg
    have hmap := coarseBinaryMap_rep
      (coarseContributionWithWork threshold.1 (coarseChildAllowanceWithWork q allowance).1)
      (coarseThresholdContribution (coarseChildThreshold B q allowance.value draw) (allowance.value / q))
      (by
        intro a
        rw [coarseContributionWithWork_value, hs]
        exact congrArg (fun t => coarseThresholdContribution t (allowance.value / q) a.value) (ht draw))
      (coarseBinaryPenaltyWithWork two evaluated.1).1 (coarseStoredPenalty ratEvaluated.1).1 hp
    have hmg := coarseBinaryMap_grid
      (coarseContributionWithWork threshold.1 (coarseChildAllowanceWithWork q allowance).1)
      (coarseBinaryPenaltyWithWork two evaluated.1).1 two.representation.den hpg (by
        intro a hden
        exact (coarseContributionWithWork_den _ _ a
          (((coarseChildAllowanceWithWork_den q allowance).trans ha).trans hden.symm)).trans hden)
    have hr := ih (fun child draw below hmem => he child draw below (List.mem_cons_of_mem _ hmem))
      (start + child.word.length)
    have hrg := coarseBinaryChildren_grid k q L two
      (fun child => coarseBinaryEval k q L frame two child) allowance rest
      (start + child.word.length) ha (by
        intro child draw below _ a s had
        exact coarseBinaryEval_grid k q L frame two child below a s had)
    exact coarseBinaryAdd_rep _ _ _ _ two.representation.den hmap hr hmg hrg

end BinaryFraction
end EditApproximation

end OAI
