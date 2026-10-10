import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayRepresentation
import OAI.Combinatorics.EditApproximation.Coarse.CoarseThresholdStep
import OAI.Combinatorics.EditApproximation.Coarse.CoarseGridTransfers

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Shared evaluation of each child, followed by its exact two-pass
penalty transform, threshold contribution and fixed-grid addition. -/
def coarseBinaryChildren {B d : ℕ} {α : Type*} (k q L : ℕ) (two : BinaryFraction)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ) (allowance : BinaryFraction) :
    List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d) → ℕ → CoarseBinaryArray × ℕ
  | [], _ => (none, 0)
  | (child, draw, below) :: rest, start =>
    let threshold := coarseChildThresholdWithWork B q allowance draw
    let childAllowance := coarseChildAllowanceWithWork L threshold.1
    let evaluated := evaluate child below childAllowance.1 start
    let penalty := coarseBinaryPenaltyWithWork two evaluated.1
    let scale := coarseChildAllowanceWithWork q allowance
    let contribution := coarseBinaryMapWithWork (coarseContributionWithWork threshold.1 scale.1) penalty.1
    let remainder := coarseBinaryChildren k q L two evaluate allowance rest (start + child.word.length)
    let total := coarseBinaryAddWithWork contribution.1 remainder.1
    (total.1, threshold.2 + childAllowance.2 + evaluated.2 + penalty.2 + scale.2 + contribution.2 +
      remainder.2 + total.2 + Nat.size start + Nat.size child.word.length + 9)

/-- Binary implementation of the pruning-stopped shared-array evaluator.
The complete tree is a semantic indexed source; visited child descriptors
carry their source offset and length, charged in `coarseBinaryChildren`. -/
def coarseBinaryEval {B : ℕ} {α : Type*} [DecidableEq α]
    (k q L : ℕ) (frame : List (Option α)) (two : BinaryFraction) :
    {d : ℕ} → CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ
  | _, tree, draws, allowance, start =>
    let prune := leWithWork (nat tree.word.length) allowance
    if prune.1 then (none, prune.2 + Nat.size tree.word.length + 1) else
    match tree, draws with
    | .leaf letter, _ =>
      let cells := arithmeticMapWithWork (fun shift : Fin (2 * k + 1) =>
        coarseGridNatWithWork allowance.denominator allowance.denominator_pos
          (coarseShiftCost k frame (.leaf (B := B) letter) start shift)) (List.finRange (2 * k + 1))
      (some cells.1, prune.2 + cells.2 + Nat.size tree.word.length + 3 * (2 * k + 1) + 1)
    | .branch children, (draws, below) =>
      let result := coarseBinaryChildren k q L two
        (fun child => coarseBinaryEval k q L frame two child) allowance
        (List.ofFn fun i => (children i, draws i, below i)) start
      (result.1, result.2 + prune.2 + Nat.size tree.word.length + B + 1)

end BinaryFraction
end EditApproximation

end OAI
