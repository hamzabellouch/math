import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedKernelWork
import OAI.Combinatorics.EditApproximation.Geometry.PreparedLocalGroupPolynomial
import OAI.Combinatorics.EditApproximation.Geometry.PreparedShellPolynomial

namespace OAI

/-! One fixed degree bounds every Boolean operation of the complete local
refinement kernel, after primitive word and finite-grid bounds are supplied. -/

namespace EditApproximation

attribute [local irreducible] representativeShellDegree preparedLocalGroupBitDegree
  onlineShellDegree physicalShellDegree

def preparedKernelBitDegree : ℕ :=
  max representativeShellDegree (max preparedLocalGroupBitDegree (max onlineShellDegree physicalShellDegree)) + 3

theorem preparedKernelBitBudget_fixedPower (N M P F exponent eM eF B X : ℕ)
    (hX : 2 ≤ X) (hN : Nat.size N ≤ B) (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X)
    (he : exponent ≤ X) (htheta : 2 ^ exponent ≤ X) (hword : 16 * B + 200 ≤ X)
    (hscales : 7 + eM + eF ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCartesian : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X)
    (hrepCount : (B + 1) * (64 * F * P + 2) ^ 2 ≤ X)
    (hgroupCount : (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ≤ X) :
    BinaryFraction.preparedKernelBitBudget N M P F exponent eM eF B X ≤ X ^ preparedKernelBitDegree := by
  let D := max representativeShellDegree
    (max preparedLocalGroupBitDegree (max onlineShellDegree physicalShellDegree))
  have hB : B ≤ X := by omega
  have hr := (localRepresentativesBitBudget_fixedPower P F B X hX hP hF hB).trans
    (Nat.pow_le_pow_right (by omega : 0 < X) (show representativeShellDegree ≤ D by
      exact Nat.le_max_left _ _))
  have hg := (preparedLocalGroupsBitBudget_fixedPower N M P F exponent eM eF B X hX hN hM hP hF
    he htheta hword hscales hV hCartesian).trans
      (Nat.pow_le_pow_right (by omega : 0 < X) (show preparedLocalGroupBitDegree ≤ D by
        exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
  have ho := (preparedLocalOnlineBitBudget_fixedPower M P B X hX hM hB hV).trans
    (Nat.pow_le_pow_right (by omega : 0 < X) (show onlineShellDegree ≤ D by
      exact (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))
  have hp := (physicalContinuationBitBudget_fixedPower M P _ _ (B + 1) (B + 4) X hX hM hP
    hrepCount hgroupCount (by omega) (by omega) hV hCartesian).trans
      (Nat.pow_le_pow_right (by omega : 0 < X) (show physicalShellDegree ≤ D by
        exact (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))
  have hone : 1 ≤ X ^ D := Nat.succ_le_of_lt (pow_pos (by omega : 0 < X) D)
  have height : 8 ≤ X ^ 3 := by
    calc
      8 = (2 : ℕ) ^ 3 := by decide
      _ ≤ X ^ 3 := Nat.pow_le_pow_left hX 3
  calc
    _ ≤ 4 * X ^ D + 4 := by unfold BinaryFraction.preparedKernelBitBudget; omega
    _ ≤ 8 * X ^ D := by omega
    _ ≤ X ^ 3 * X ^ D := Nat.mul_le_mul_right _ height
    _ = X ^ preparedKernelBitDegree := by
      rw [← pow_add]
      change X ^ (3 + D) = X ^ (D + 3)
      rw [Nat.add_comm 3 D]

end EditApproximation

end OAI
