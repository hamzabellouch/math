import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryEvaluation
import OAI.Combinatorics.EditApproximation.Coarse.CoarseArraySimulation

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseBinaryChildren_grid {B d : ℕ} {α : Type*} (k q L : ℕ) (two : BinaryFraction)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ) (allowance : BinaryFraction)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d)) (start : ℕ)
    (ha : allowance.representation.den = two.representation.den)
    (he : ∀ child draw below, (child, draw, below) ∈ children → ∀ (a : BinaryFraction) (s : ℕ),
      a.representation.den = two.representation.den → CoarseArrayOnGrid two.representation.den
        (evaluate child below a s).1) :
    CoarseArrayOnGrid two.representation.den
      (coarseBinaryChildren k q L two evaluate allowance children start).1 := by
  induction children generalizing start with
  | nil => intro values hv; cases hv
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have ht := (coarseChildThresholdWithWork_den B q allowance draw).trans ha
    have hc := (coarseChildAllowanceWithWork_den L (coarseChildThresholdWithWork B q allowance draw).1).trans ht
    have hev := he child draw below List.mem_cons_self
      (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance draw).1).1 start hc
    have hp := coarseBinaryPenalty_grid two _ hev
    have hs := (coarseChildAllowanceWithWork_den q allowance).trans ha
    have hm := coarseBinaryMap_grid
      (coarseContributionWithWork (coarseChildThresholdWithWork B q allowance draw).1
        (coarseChildAllowanceWithWork q allowance).1)
      (coarseBinaryPenaltyWithWork two
        (evaluate child below (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance draw).1).1 start).1).1
      two.representation.den hp (by
        intro z hz
        exact (coarseContributionWithWork_den _ _ z (hs.trans hz.symm)).trans hz)
    have hr := ih (start + child.word.length)
      (fun child draw below hmem => he child draw below (List.mem_cons_of_mem _ hmem))
    exact coarseBinaryAdd_grid _ _ _ hm hr

 theorem coarseBinaryEval_grid {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L : ℕ) (frame : List (Option α)) (two : BinaryFraction)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d)
    (allowance : BinaryFraction) (start : ℕ)
    (ha : allowance.representation.den = two.representation.den) :
    CoarseArrayOnGrid two.representation.den
      (coarseBinaryEval k q L frame two tree draws allowance start).1 := by
  induction tree generalizing allowance start with
  | leaf letter =>
    rw [coarseBinaryEval]
    split_ifs
    · intro values hv; cases hv
    · intro values hv a hamem
      have heq : (arithmeticMapWithWork (fun shift : Fin (2 * k + 1) =>
          coarseGridNatWithWork allowance.denominator allowance.denominator_pos
            (coarseShiftCost k frame (.leaf (B := B) letter) start shift))
          (List.finRange (2 * k + 1))).1 = values := Option.some.inj hv
      rw [← heq, arithmeticMapWithWork_value] at hamem
      obtain ⟨shift, _, rfl⟩ := List.mem_map.mp hamem
      exact (coarseGridNatWithWork_den _ _ _).trans ha
  | branch children ih =>
    obtain ⟨draws, below⟩ := draws
    rw [coarseBinaryEval]
    split_ifs
    · intro values hv; cases hv
    · apply coarseBinaryChildren_grid k q L two _ allowance _ start ha
      intro child draw childBelow hmem a s hag
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
      cases hi
      exact ih i (below i) a s hag

end BinaryFraction
end EditApproximation

end OAI
