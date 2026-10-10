import OAI.Combinatorics.EditApproximation.Coarse.CoarseReadBudget
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedCostComparison
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexBudget

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseIndexedExtra coarseBinaryWeight

theorem coarseIndexedExtra_bound {B : ℕ} (R k q L n K : ℕ) (source target : List ℕ)
    (two : BinaryFraction) (hB : 0 < B) (hK : 1 ≤ K)
    (hs : source.length ≤ n) (budget : CoarseReadBudget B R k n source target K)
    (d offset : ℕ) (draws : CoarseThresholdDraws B d) (allowance : BinaryFraction)
    (start : ℕ) (hd : d ≤ R) (hoff : offset + B ^ d ≤ B ^ R)
    (hstart : start + coarseDescriptorLength B d n offset ≤ n) :
    coarseIndexedExtra k q L n source target two d offset draws allowance start ≤
      (32 * K) * coarseBinaryWeight k q L
        (coarseReadTree B d (fun j => coarsePaddedRead n source (offset + j))) draws allowance := by
  induction d generalizing offset allowance start with
  | zero =>
    have ho : offset ≤ B ^ R := by omega
    have hdesc := budget.descriptor 0 hd offset ho
    have hread := budget.sourceRead offset ho
    have hsum : ((List.finRange (2 * k + 1)).map fun shift =>
        (coarseReadShiftWithWork k n target (coarsePaddedRead n source offset) start shift).2).sum ≤
        (2 * k + 1) * K := by
      calc
        _ ≤ ((List.finRange (2 * k + 1)).map fun _ => K).sum :=
          List.sum_le_sum (fun shift _ => budget.mismatch offset ho start (by omega) shift)
        _ = (2 * k + 1) * K := by simp
    have hlen := coarseReadTree_padded_length B 0 n offset source hs
    simp only [coarseReadTree, Nat.add_zero] at hlen ⊢
    rw [coarseIndexedExtra, coarseBinaryWeight, hlen]
    split_ifs
    · nlinarith only [hdesc, hK]
    · simp only [coarsePaddedReadWithWork_value]
      have hb : 2 * k + 1 ≤ B * (2 * k + 1) := Nat.le_mul_of_pos_left _ hB
      nlinarith only [hdesc, hread, hsum, hK, Nat.mul_le_mul_right K hb]
  | succ d ih =>
    obtain ⟨draws, below⟩ := draws
    have ho : offset ≤ B ^ R := by omega
    let children := fun i : Fin B => coarseReadTree B d
      (fun j => coarsePaddedRead n source (offset + i.val * B ^ d + j))
    let width := fun i : Fin B => coarseDescriptorLength B d n (offset + i.val * B ^ d)
    let weight := fun i : Fin B => coarseBinaryWeight k q L (children i) (below i)
    have htree : coarseReadTree B (d + 1) (fun j => coarsePaddedRead n source (offset + j)) =
        CoarseSourceTree.branch children := by
      simp only [coarseReadTree, children, Nat.add_assoc]
    have hlen : (CoarseSourceTree.branch children).word.length =
        coarseDescriptorLength B (d + 1) n offset := by
      rw [← htree]
      exact coarseReadTree_padded_length B (d + 1) n offset source hs
    have hwidth (i : Fin B) : width i = (children i).word.length :=
      (coarseReadTree_padded_length B d n (offset + i.val * B ^ d) source hs).symm
    have hchild (i : Fin B) : offset + i.val * B ^ d + B ^ d ≤ B ^ R := by
      have hm := Nat.mul_le_mul_right (B ^ d) (Nat.succ_le_of_lt i.isLt)
      rw [pow_succ] at hoff
      nlinarith only [hm, hoff]
    let extra := fun i : Fin B => fun a s =>
      coarseIndexedExtra k q L n source target two d (offset + i.val * B ^ d) (below i) a s +
        3 * ((coarseChildOffsetWithWork offset (B ^ d) i.val).2 +
          (coarseDescriptorWithWork B d n (offset + i.val * B ^ d)).2 +
          (binaryNaturalAddWithWork s (width i)).2 + 3)
    have hc : ∀ i ∈ List.finRange B, ∀ s, s + width i ≤ n →
        extra i (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance (draws i)).1).1 s ≤
        (32 * K) * weight i (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance (draws i)).1).1 + 18 * K := by
      intro i _ s hsi
      have hc := ih (offset + i.val * B ^ d) (below i)
        (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance (draws i)).1).1 s (by omega) (hchild i) hsi
      have h1 := budget.offset offset ho i d (by omega)
      have h2 := budget.descriptor d (by omega) (offset + i.val * B ^ d) (by have := hchild i; omega)
      have h3 := budget.advance s (by omega) (width i) (by omega)
      change _ ≤ (32 * K) * weight i _ at hc
      dsimp only [extra]
      omega
    have hspan : coarseIndexSpan width (List.finRange B) =
        coarseDescriptorLength B (d + 1) n offset := by
      rw [coarseIndexSpan_eq width children draws below hwidth, ← List.ofFn_eq_map,
        coarseChildrenSpan_ofFn, hlen]
    have hloop := coarseIndexAdditionalWork_bound q L n (32 * K) (18 * K) width draws extra weight
      allowance (List.finRange B) hc start (by rw [hspan]; exact hstart)
    have hw := coarseIndexWeight_eq k q L children draws below allowance (List.finRange B)
    have hdesc := budget.descriptor (d + 1) hd offset ho
    have hpower := budget.power d (by omega)
    erw [htree, coarseIndexedExtra, coarseBinaryWeight, hlen]
    split_ifs
    · nlinarith only [hdesc, hK]
    · simp only [bitPowerWithWork_value, bitWordValue_bits, coarseChildOffsetWithWork_value,
        coarseDescriptorWithWork_value]
      change _ ≤ (32 * K) * (B * (2 * k + 1) + 1 + _)
      simp only [List.length_finRange] at hloop
      dsimp only [extra, width, weight] at hloop
      rw [hw, ← List.ofFn_eq_map] at hloop
      have hbase : 18 * K * B ≤ (32 * K) * (B * (2 * k + 1)) := by
        calc
          _ ≤ (32 * K) * B := by nlinarith only [Nat.zero_le (K * B)]
          _ ≤ _ := Nat.mul_le_mul_left (32 * K)
            (Nat.le_mul_of_pos_right B (by omega))
      nlinarith only [hloop, hdesc, hpower, hbase, hK]

end BinaryFraction
end EditApproximation

end OAI
