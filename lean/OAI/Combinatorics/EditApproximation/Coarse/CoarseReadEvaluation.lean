import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadCore

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseReadCore coarseBinaryEval

theorem coarseReadCore_eq {B : ℕ} {α : Type*} [DecidableEq α]
    (k q L n : ℕ) (source target : List α) (hs : source.length ≤ n) (ht : target.length ≤ n)
    (two : BinaryFraction) (d offset : ℕ) (draws : CoarseThresholdDraws B d)
    (allowance : BinaryFraction) (start : ℕ) :
    coarseReadCore k q L n source target two d offset draws allowance start =
      coarseBinaryEval k q L (coarseTargetFrame k (coarsePadTo n target)) two
        (coarseReadTree B d (fun i => coarsePaddedRead n source (offset + i))) draws allowance start := by
  induction d generalizing offset allowance start with
  | zero =>
    have hlen := coarseReadTree_padded_length B 0 n offset source hs
    simp only [coarseReadTree, Nat.add_zero] at hlen ⊢
    rw [coarseReadCore, coarseBinaryEval, hlen]
    simp only [coarseReadShiftCost_eq k n target ht]
  | succ d ih =>
    obtain ⟨draws, below⟩ := draws
    let children := fun i : Fin B => coarseReadTree B d
      (fun j => coarsePaddedRead n source (offset + i.val * B ^ d + j))
    have htree : coarseReadTree B (d + 1) (fun i => coarsePaddedRead n source (offset + i)) =
        CoarseSourceTree.branch children := by
      simp only [coarseReadTree, children, Nat.add_assoc]
    have hlen : (CoarseSourceTree.branch children).word.length =
        coarseDescriptorLength B (d + 1) n offset := by
      rw [← htree]
      exact coarseReadTree_padded_length B (d + 1) n offset source hs
    have hloop : coarseIndexChildren k q L two
        (fun i => coarseDescriptorLength B d n (offset + i.val * B ^ d))
        (fun i => coarseReadCore k q L n source target two d (offset + i.val * B ^ d) (below i))
        draws allowance (List.finRange B) start =
      coarseBinaryChildren k q L two
        (fun child => coarseBinaryEval k q L (coarseTargetFrame k (coarsePadTo n target)) two child)
        allowance (List.ofFn fun i => (children i, draws i, below i)) start := by
      simpa only [List.ofFn_eq_map] using coarseIndexChildren_eq k q L two _ children _ _ draws below
        (fun i => (coarseReadTree_padded_length B d n (offset + i.val * B ^ d) source hs).symm)
        (fun i a s => ih (offset + i.val * B ^ d) (below i) a s) allowance (List.finRange B) start
    erw [htree, coarseReadCore, coarseBinaryEval, hlen]
    simp only [hloop]

end BinaryFraction
end EditApproximation

end OAI
