import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryBox
import OAI.Combinatorics.EditApproximation.Coarse.CoarseScalarBounds
import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryWeight

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseBinaryChildren_bounds {B d : ℕ} {α : Type*} (k q L N V D A : ℕ)
    (two allowance : BinaryFraction)
    (evaluate : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ →
      CoarseBinaryArray × ℕ)
    (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (hB : 0 < B) (hlen : children.length ≤ B) (htwo : two.value = 2) (htw : two.width ≤ A)
    (ha : allowance.width ≤ A) (hBbits : Nat.size B + 2 ≤ A)
    (hqbits : Nat.size q + 2 ≤ A) (hLbits : Nat.size L + 2 ≤ A)
    (hNbits : Nat.size N ≤ A)
    (ht : ∀ draw : Fin B, (coarseChildThresholdWithWork B q allowance draw).1.width ≤ A)
    (hs : CoarseGridCell two (coarseChildAllowanceWithWork q allowance).1 k D A)
    (hbound : Nat.size (B * (V + k) + 2) + 2 * D + 1 ≤ A)
    (he : ∀ child draw below, (child, draw, below) ∈ children → ∀ s,
      s + child.word.length ≤ N →
      CoarseBinaryBox two (2 * k + 1) V D A
        (evaluate child below (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance draw).1).1 s).1 ∧
      (evaluate child below (coarseChildAllowanceWithWork L
          (coarseChildThresholdWithWork B q allowance draw).1).1 s).2 ≤
        (100000000 * (A + 1) ^ 2) * weight child below
          (coarseChildAllowanceWithWork L (coarseChildThresholdWithWork B q allowance draw).1).1)
    (start : ℕ) (hstart : start + coarseChildrenSpan children ≤ N) :
    CoarseBinaryBox two (2 * k + 1) (children.length * (V + k)) D A
      (coarseBinaryChildren k q L two evaluate allowance children start).1 ∧
    (coarseBinaryChildren k q L two evaluate allowance children start).2 + children.length ≤
      (100000000 * (A + 1) ^ 2) *
        (coarseBinaryChildrenWeight q L weight allowance children + (2 * k + 1) * children.length) := by
  have hvsmall : V + 2 ≤ B * (V + k) + 2 := by nlinarith
  have hvbound : Nat.size (V + 2) + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size hvsmall) _) _).trans hbound
  have hmapbound : Nat.size (V + k) + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size (by nlinarith : V + k ≤ B * (V + k) + 2)) _) _).trans hbound
  induction children generalizing start with
  | nil =>
    constructor
    · exact coarseBinaryBox_none _ _ _ _ _
    · simp only [coarseBinaryChildren, coarseBinaryChildrenWeight, List.length_nil, mul_zero, add_zero, le_refl]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have hspan : start + (child.word.length + coarseChildrenSpan rest) ≤ N := hstart
    have hchild := he child draw below List.mem_cons_self start (by omega)
    have hrest := ih (by simp only [List.length_cons] at hlen; omega)
      (fun child draw below hmem => he child draw below (List.mem_cons_of_mem _ hmem))
      (start + child.word.length) (by omega)
    let threshold := coarseChildThresholdWithWork B q allowance draw
    let childAllowance := coarseChildAllowanceWithWork L threshold.1
    let evaluated := evaluate child below childAllowance.1 start
    let penalty := coarseBinaryPenaltyWithWork two evaluated.1
    let scale := coarseChildAllowanceWithWork q allowance
    let contribution := coarseBinaryMapWithWork (coarseContributionWithWork threshold.1 scale.1) penalty.1
    let remainder := coarseBinaryChildren k q L two evaluate allowance rest (start + child.word.length)
    have hpen : CoarseBinaryBox two (2 * k + 1) V D A penalty.1 :=
      coarseBinaryPenaltyWithWork_box two _ V D A evaluated.1 hchild.1 htwo htw hvbound
    have hcon : CoarseBinaryBox two (2 * k + 1) (V + k) D A contribution.1 :=
      coarseBinaryMapWithWork_box two _ V (V + k) D A _ penalty.1 hpen
        (fun a ha => coarseContributionWithWork_bounds two threshold.1 scale.1 a V k D A ha hs hmapbound)
    have habound : Nat.size ((V + k) + rest.length * (V + k)) + 2 * D + 1 ≤ A := by
      apply le_trans _ hbound
      apply Nat.add_le_add_right
      apply Nat.add_le_add_right
      apply Nat.size_le_size
      simp only [List.length_cons] at hlen
      nlinarith
    constructor
    · have hh := coarseBinaryAddWithWork_box two (2 * k + 1) (V + k) (rest.length * (V + k)) D A
        contribution.1 remainder.1 hcon hrest.1 habound
      change CoarseBinaryBox two (2 * k + 1) ((rest.length + 1) * (V + k)) D A
        (coarseBinaryAddWithWork contribution.1 remainder.1).1
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using hh
    · have htc := coarseChildThresholdWithWork_cost B q A allowance draw ha hBbits hqbits
      have hlc := coarseChildAllowanceWithWork_cost L A threshold.1 (ht draw) hLbits
      have hsc := coarseChildAllowanceWithWork_cost q A allowance ha hqbits
      have hpc := coarseBinaryPenaltyWithWork_cost two (2 * k + 1) V D A evaluated.1 hchild.1 htwo htw hvbound
      have hmc := coarseBinaryMapWithWork_cost two (2 * k + 1) V D A (2200 * (A + 1) ^ 2)
        (coarseContributionWithWork threshold.1 scale.1) penalty.1 hpen
        (fun a ha => coarseContributionWithWork_cost threshold.1 scale.1 a A
          (ht draw) hs.2.2.2.2 ha.2.2.2.2)
      have hac := coarseBinaryAddWithWork_cost two (2 * k + 1) (V + k) (rest.length * (V + k)) D A
        contribution.1 remainder.1 hcon hrest.1
      have haddr : Nat.size start ≤ A := (Nat.size_le_size (by omega)).trans hNbits
      have hchildlen : Nat.size child.word.length ≤ A := (Nat.size_le_size (by omega)).trans hNbits
      have hstep : threshold.2 + childAllowance.2 + penalty.2 + scale.2 + contribution.2 +
          (coarseBinaryAddWithWork contribution.1 remainder.1).2 +
          Nat.size start + Nat.size child.word.length + 10 ≤
          100000000 * (A + 1) ^ 2 * (2 * k + 1) := by
        nlinarith only [htc, hlc, hsc, hpc, hmc, hac, haddr, hchildlen,
          Nat.zero_le A, Nat.zero_le k]
      change threshold.2 + childAllowance.2 + evaluated.2 + penalty.2 + scale.2 + contribution.2 +
        remainder.2 + (coarseBinaryAddWithWork contribution.1 remainder.1).2 +
        Nat.size start + Nat.size child.word.length + 9 + (rest.length + 1) ≤ _
      have heval := hchild.2
      change evaluated.2 ≤ _ at heval
      have hrec := hrest.2
      change remainder.2 + rest.length ≤ _ at hrec
      simp only [coarseBinaryChildrenWeight, List.length_cons]
      nlinarith only [hstep, heval, hrec]

end BinaryFraction
end EditApproximation

end OAI
