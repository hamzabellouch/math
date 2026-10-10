import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedChildren
import OAI.Combinatorics.EditApproximation.Coarse.CoarseDescriptorWork

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseReadShiftCost {α : Type*} [DecidableEq α] (k n : ℕ) (target : List α)
    (letter : Option (Option α)) (start : ℕ) (shift : Fin (2 * k + 1)) : ℕ :=
  match letter with
  | none => 0
  | some letter => if coarseFramedRead k n target (start + shift.val) = some letter then 0 else 1

theorem coarseReadShiftCost_eq {B : ℕ} {α : Type*} [DecidableEq α]
    (k n : ℕ) (target : List α) (hn : target.length ≤ n)
    (letter : Option (Option α)) (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseShiftCost k (coarseTargetFrame k (coarsePadTo n target))
      (.leaf (B := B) letter) start shift = coarseReadShiftCost k n target letter start shift := by
  cases letter with
  | none => rfl
  | some letter =>
    unfold coarseShiftCost coarseReadShiftCost
    rw [coarseFramedRead_value k n target hn]

/-- Core arithmetic over source descriptors. The separate descriptor/read
counter charges address arithmetic and original-array accesses. -/
def coarseReadCore {B : ℕ} {α : Type*} [DecidableEq α]
    (k q L n : ℕ) (source target : List α) (two : BinaryFraction) :
    (d : ℕ) → (offset : ℕ) → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ
  | 0, offset, _, allowance, start =>
    let size := coarseDescriptorLength B 0 n offset
    let prune := leWithWork (nat size) allowance
    if prune.1 then (none, prune.2 + Nat.size size + 1) else
    let cells := arithmeticMapWithWork (fun shift : Fin (2 * k + 1) =>
      coarseGridNatWithWork allowance.denominator allowance.denominator_pos
        (coarseReadShiftCost k n target (coarsePaddedRead n source offset) start shift))
      (List.finRange (2 * k + 1))
    (some cells.1, prune.2 + cells.2 + Nat.size size + 3 * (2 * k + 1) + 1)
  | d + 1, offset, (draws, below), allowance, start =>
    let size := coarseDescriptorLength B (d + 1) n offset
    let prune := leWithWork (nat size) allowance
    if prune.1 then (none, prune.2 + Nat.size size + 1) else
    let result := coarseIndexChildren k q L two
      (fun i => coarseDescriptorLength B d n (offset + i.val * B ^ d))
      (fun i => coarseReadCore k q L n source target two d (offset + i.val * B ^ d) (below i))
      draws allowance (List.finRange B) start
    (result.1, result.2 + prune.2 + Nat.size size + B + 1)

end BinaryFraction
end EditApproximation

end OAI
