import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayHistory

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseIndexArrayHistory {B : ℕ} (k q L : ℕ) (two : BinaryFraction)
    (width : Fin B → ℕ) (evaluate : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (history : Fin B → BinaryFraction → ℕ → ℕ)
    (draw : Fin B → Fin B) (allowance : BinaryFraction) : List (Fin B) → ℕ → ℕ
  | [], _ => 0
  | i :: rest, start =>
    let threshold := (coarseChildThresholdWithWork B q allowance (draw i)).1
    let childAllowance := (coarseChildAllowanceWithWork L threshold).1
    let evaluated := (evaluate i childAllowance start).1
    let penalty := (coarseBinaryPenaltyWithWork two evaluated).1
    let scale := (coarseChildAllowanceWithWork q allowance).1
    let contribution := (coarseBinaryMapWithWork (coarseContributionWithWork threshold scale) penalty).1
    let remainder := (coarseIndexChildren k q L two width evaluate draw allowance rest (start + width i)).1
    let total := (coarseBinaryAddWithWork contribution remainder).1
    history i childAllowance start +
      coarseIndexArrayHistory k q L two width evaluate history draw allowance rest (start + width i) +
      coarseArrayStorage evaluated + coarseArrayStorage penalty +
      coarseArrayStorage contribution + coarseArrayStorage total

theorem coarseIndexArrayHistory_eq {B d : ℕ} {α : Type*}
    (k q L : ℕ) (two : BinaryFraction) (width : Fin B → ℕ)
    (children : Fin B → CoarseSourceTree B α d)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ)
    (history : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ → ℕ)
    (indexed : Fin B → BinaryFraction → ℕ → CoarseBinaryArray × ℕ)
    (indexedHistory : Fin B → BinaryFraction → ℕ → ℕ)
    (draw : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B d)
    (hw : ∀ i, width i = (children i).word.length)
    (he : ∀ i a s, (indexed i a s).1 = (evaluate (children i) (below i) a s).1)
    (hh : ∀ i a s, indexedHistory i a s = history (children i) (below i) a s)
    (allowance : BinaryFraction) (indices : List (Fin B)) (start : ℕ) :
    coarseIndexArrayHistory k q L two width indexed indexedHistory draw allowance indices start =
      coarseChildrenArrayHistory k q L two evaluate history allowance
        (indices.map fun i => (children i, draw i, below i)) start := by
  have harray (indices : List (Fin B)) (start : ℕ) :
      (coarseIndexChildren k q L two width indexed draw allowance indices start).1 =
      (coarseBinaryChildren k q L two evaluate allowance
        (indices.map fun i => (children i, draw i, below i)) start).1 := by
    calc
      _ = (coarseIndexChildren k q L two width
          (fun i => evaluate (children i) (below i)) draw allowance indices start).1 :=
        coarseIndexChildren_value_congr k q L two width draw indexed
          (fun i => evaluate (children i) (below i)) he allowance indices start
      _ = _ := congrArg Prod.fst (coarseIndexChildren_eq k q L two width children evaluate
        (fun i => evaluate (children i) (below i)) draw below hw (fun _ _ _ => rfl) allowance indices start)
  induction indices generalizing start with
  | nil => rfl
  | cons i rest ih =>
    simp only [coarseIndexArrayHistory, coarseChildrenArrayHistory, List.map_cons, he, hh, harray, hw, ih]

/-- Every array footprint of the literal indexed recursion. Descriptor
and address words are charged separately by the indexed bit counter. -/
def coarseIndexedArrayHistory {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) : (d offset : ℕ) → CoarseThresholdDraws B d → BinaryFraction → ℕ → ℕ
  | 0, offset, draws, allowance, start =>
    if (leWithWork (nat (coarseDescriptorLength B 0 n offset)) allowance).1 then 1 else
      coarseArrayStorage (coarseIndexedWithWork k q L n source target two 0 offset draws allowance start).1
  | d + 1, offset, (draws, below), allowance, start =>
    if (leWithWork (nat (coarseDescriptorLength B (d + 1) n offset)) allowance).1 then 1 else
      coarseArrayStorage (coarseIndexedWithWork k q L n source target two (d + 1) offset
        (draws, below) allowance start).1 +
      coarseIndexArrayHistory k q L two
        (fun i => coarseDescriptorLength B d n (offset + i.val * B ^ d))
        (fun i => coarseIndexedWithWork k q L n source target two d (offset + i.val * B ^ d) (below i))
        (fun i => coarseIndexedArrayHistory k q L n source target two d (offset + i.val * B ^ d) (below i))
        draws allowance (List.finRange B) start

attribute [local irreducible] coarseIndexedArrayHistory coarseBinaryArrayHistory

theorem coarseIndexedArrayHistory_eq {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (hs : source.length ≤ n) (ht : target.length ≤ n) (two : BinaryFraction)
    (d offset : ℕ) (draws : CoarseThresholdDraws B d) (allowance : BinaryFraction) (start : ℕ) :
    coarseIndexedArrayHistory k q L n source target two d offset draws allowance start =
      coarseBinaryArrayHistory k q L (coarseTargetFrame k (coarsePadTo n target)) two
        (coarseReadTree B d (fun i => coarsePaddedRead n source (offset + i))) draws allowance start := by
  have hvalue (d offset : ℕ) (draws : CoarseThresholdDraws B d) (a : BinaryFraction) (s : ℕ) :
      (coarseIndexedWithWork k q L n source target two d offset draws a s).1 =
        (coarseBinaryEval k q L (coarseTargetFrame k (coarsePadTo n target)) two
          (coarseReadTree B d (fun i => coarsePaddedRead n source (offset + i))) draws a s).1 := by
    rw [coarseIndexedWithWork_value, coarseReadCore_eq k q L n source target hs ht]
  induction d generalizing offset allowance start with
  | zero =>
    have hlen := coarseReadTree_padded_length B 0 n offset source hs
    rw [coarseIndexedArrayHistory]
    simp only [coarseReadTree, Nat.add_zero] at hlen ⊢
    rw [coarseBinaryArrayHistory, hlen]
    split_ifs
    · rfl
    · simpa only [coarseReadTree, Nat.add_zero] using
        congrArg coarseArrayStorage (hvalue 0 offset draws allowance start)
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
    have hloop := coarseIndexArrayHistory_eq k q L two
      (fun i => coarseDescriptorLength B d n (offset + i.val * B ^ d)) children
      (fun child => coarseBinaryEval k q L (coarseTargetFrame k (coarsePadTo n target)) two child)
      (fun child => coarseBinaryArrayHistory k q L (coarseTargetFrame k (coarsePadTo n target)) two child)
      (fun i => coarseIndexedWithWork k q L n source target two d (offset + i.val * B ^ d) (below i))
      (fun i => coarseIndexedArrayHistory k q L n source target two d (offset + i.val * B ^ d) (below i))
      draws below
      (fun i => (coarseReadTree_padded_length B d n (offset + i.val * B ^ d) source hs).symm)
      (fun i a s => hvalue d (offset + i.val * B ^ d) (below i) a s)
      (fun i a s => ih (offset + i.val * B ^ d) (below i) a s)
      allowance (List.finRange B) start
    rw [htree, coarseIndexedArrayHistory, coarseBinaryArrayHistory, hlen]
    split_ifs
    · rfl
    · have hroot := congrArg coarseArrayStorage
        (hvalue (d + 1) offset (draws, below) allowance start)
      rw [htree] at hroot
      exact congrArg₂ Nat.add hroot (by simpa only [List.ofFn_eq_map] using hloop)

end BinaryFraction
end EditApproximation

end OAI
