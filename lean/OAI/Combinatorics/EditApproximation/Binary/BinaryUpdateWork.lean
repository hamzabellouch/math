import OAI.Combinatorics.EditApproximation.Binary.BinaryMaximizerWork

namespace OAI

/-! Bit cost of the actual coordinate update, including construction of
its rational step and complement. -/

namespace EditApproximation
namespace BinaryFraction

def updateCoefficientWordBudget (K : ℕ) : ℕ := Nat.size (K + 2) + 8

def updateCoordinateWordBudget (K P : ℕ) : ℕ := P + 2 * updateCoefficientWordBudget K + 8

def optimizerUpdateBitBudget (d K P : ℕ) : ℕ :=
  2100 * (Nat.size (K + 2) + 6) ^ 2 +
    (6000 * (updateCoefficientWordBudget K + 4) ^ 2 + 1) +
    d * (110000 * (updateCoordinateWordBudget K P + 1) ^ 2 + 6) + Nat.size (K + 2) + 4

theorem nat_width_le (n : ℕ) : (nat n).width ≤ Nat.size n + 2 := by
  have h := nat_width_le_storageBits n
  rw [nat_representation, UnreducedRational.storageBits_nat] at h
  exact h

theorem optimizerUpdateWithWork_cost {d : ℕ} (j K P : ℕ) (hj : j ≤ K)
    (previous selected : Vector BinaryFraction d)
    (hp : ∀ i, (previous.get i).width ≤ P) (hs : ∀ i, (selected.get i).width ≤ P) :
    (optimizerUpdateWithWork j previous selected).2 ≤ optimizerUpdateBitBudget d K P := by
  let step := divWithWork (nat 2) (nat (j + 2))
  let complement := subWithWork one step.1
  let C := updateCoefficientWordBudget K
  let W := updateCoordinateWordBudget K P
  have hsize := Nat.size_le_size (show j + 2 ≤ K + 2 by omega)
  have htwo : Nat.size 2 = 2 := by decide
  have hstep : step.1.width ≤ C := by
    have hw := divWithWork_self_width (nat 2) (nat (j + 2))
    rw [divWithWork_representation, nat_representation, nat_representation] at hw
    have hc := UnreducedRational.storageBits_div (UnreducedRational.nat 2) (UnreducedRational.nat (j + 2))
    rw [UnreducedRational.storageBits_nat, UnreducedRational.storageBits_nat] at hc
    rw [htwo] at hc
    change step.1.width ≤ _ at hw
    dsimp only [C, updateCoefficientWordBudget]
    omega
  have hstepStorage : step.1.representation.storageBits ≤ C := by
    change ((nat 2).divWithWork (nat (j + 2))).1.representation.storageBits ≤ _
    rw [divWithWork_representation, nat_representation, nat_representation]
    have h := UnreducedRational.storageBits_div (UnreducedRational.nat 2) (UnreducedRational.nat (j + 2))
    simp only [UnreducedRational.storageBits_nat] at h
    rw [htwo] at h
    dsimp only [C, updateCoefficientWordBudget]
    omega
  have hcomp : complement.1.width ≤ 2 * C + 8 := by
    have hw := canonicalAddWithWork_self_width one step.1.neg
    change complement.1.width ≤ complement.1.representation.storageBits at hw
    rw [subWithWork_representation, one_representation] at hw
    have h := UnreducedRational.storageBits_sub UnreducedRational.one step.1.representation
    rw [UnreducedRational.storageBits_one] at h
    omega
  have hcpos : 0 ≤ C := Nat.zero_le _
  have hleft (i : Fin d) := canonicalMulWithWork_cost complement.1 (previous.get i) W
    (by dsimp only [W, updateCoordinateWordBudget]; omega)
    (by dsimp only [W, updateCoordinateWordBudget]; have h := hp i; omega)
  have hright (i : Fin d) := canonicalMulWithWork_cost step.1 (selected.get i) W
    (by dsimp only [W, updateCoordinateWordBudget]; omega)
    (by dsimp only [W, updateCoordinateWordBudget]; have h := hs i; omega)
  have hleftw (i : Fin d) : (canonicalMulWithWork complement.1 (previous.get i)).1.width ≤ 4 * W + 2 := by
    have hw := canonicalMulWithWork_width_le_storageBits complement.1 (previous.get i)
    have hm := UnreducedRational.storageBits_mul complement.1.representation (previous.get i).representation
    have hc := representation_storageBits_le complement.1
    have hi := representation_storageBits_le (previous.get i)
    have hh := hp i
    dsimp only [W, updateCoordinateWordBudget]
    omega
  have hrightw (i : Fin d) : (canonicalMulWithWork step.1 (selected.get i)).1.width ≤ 4 * W + 2 := by
    have hw := canonicalMulWithWork_width_le_storageBits step.1 (selected.get i)
    have hm := UnreducedRational.storageBits_mul step.1.representation (selected.get i).representation
    have hc := representation_storageBits_le step.1
    have hi := representation_storageBits_le (selected.get i)
    have hh := hs i
    dsimp only [W, updateCoordinateWordBudget]
    omega
  have hcell (i : Fin d) :
      (canonicalMulWithWork complement.1 (previous.get i)).2 +
        (canonicalMulWithWork step.1 (selected.get i)).2 +
        (canonicalAddWithWork (canonicalMulWithWork complement.1 (previous.get i)).1
          (canonicalMulWithWork step.1 (selected.get i)).1).2 + 4 ≤
        110000 * (W + 1) ^ 2 := by
    have ha := canonicalAddWithWork_cost (canonicalMulWithWork complement.1 (previous.get i)).1
      (canonicalMulWithWork step.1 (selected.get i)).1 (4 * W + 2) (hleftw i) (hrightw i)
    nlinarith only [hleft i, hright i, ha, Nat.zero_le W]
  have hmap := vectorMapWithWork_cost_le d (fun i =>
    let first := canonicalMulWithWork complement.1 (previous.get i)
    let second := canonicalMulWithWork step.1 (selected.get i)
    let total := canonicalAddWithWork first.1 second.1
    (total.1, first.2 + second.2 + total.2 + 4)) (110000 * (W + 1) ^ 2) hcell
  have hn := nat_width_le (j + 2)
  have ht : (nat 2).width ≤ Nat.size (K + 2) + 4 := by have h := nat_width_le 2; rw [htwo] at h; omega
  have cstep := divWithWork_cost (nat 2) (nat (j + 2)) (Nat.size (K + 2) + 4) ht (by omega)
  have ccomp := subWithWork_cost one step.1 (C + 3)
    (by have h := one_width; omega) (by omega)
  change step.2 + complement.2 + (vectorMapWithWork d _).2 + Nat.size (j + 2) + 4 ≤ _
  change _ ≤ 2100 * (Nat.size (K + 2) + 6) ^ 2 + (6000 * (C + 4) ^ 2 + 1) +
    d * (110000 * (W + 1) ^ 2 + 6) + Nat.size (K + 2) + 4
  change step.2 ≤ _ at cstep
  change complement.2 ≤ _ at ccomp
  nlinarith only [cstep, ccomp, hmap, hsize]

end BinaryFraction
end EditApproximation

end OAI
