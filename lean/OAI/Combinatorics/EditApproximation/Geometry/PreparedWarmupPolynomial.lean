import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalWarmupWork
import OAI.Combinatorics.EditApproximation.Geometry.PreparedCachedKernelWork

namespace OAI

/-! The initial warmup Bellman scan and its cache return are covered by
the same fixed polynomial envelope as the full continuation. -/

namespace EditApproximation

attribute [local irreducible] representativeShellDegree physicalShellDegree
  preparedCacheReturnBitDegree

private theorem warmup_le_continuation (M P F B : ℕ) :
    BinaryFraction.localWarmupBitBudget M P F B ≤
      BinaryFraction.localRepresentativesBitBudget P F B +
        BinaryFraction.physicalContinuationBitBudget M P ((B + 1) * (64 * F * P + 2) ^ 2)
          0 0 (B + 4) + 3 := by
  unfold BinaryFraction.localWarmupBitBudget BinaryFraction.physicalContinuationBitBudget
    BinaryFraction.localContinuationBitBudget
  dsimp only
  simp only [Nat.zero_mul, Nat.add_assoc, Nat.reduceAdd]
  omega

private theorem warmup_width_le_continuation (M B : ℕ) :
    BinaryFraction.localWarmupWordBudget M B ≤ BinaryFraction.preparedKernelWordBudget M B := by
  unfold BinaryFraction.localWarmupWordBudget BinaryFraction.preparedKernelWordBudget
    BinaryFraction.localContinuationWordBudget BinaryFraction.localContinuationInputBudget
    BinaryFraction.refinementUpdateWordBudget
  dsimp only
  omega

def preparedWarmupBitDegree : ℕ :=
  max representativeShellDegree (max physicalShellDegree preparedCacheReturnBitDegree) + 3

theorem cachedWarmupBitBudget_fixedPower (M P F B X : ℕ) (hX : 2 ≤ X)
    (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X) (hB : B + 4 ≤ X)
    (hrep : (B + 1) * (64 * F * P + 2) ^ 2 ≤ X)
    (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCartesian : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    BinaryFraction.localWarmupBitBudget M P F B +
        BinaryFraction.powerDenominatorBitBudget 0 (BinaryFraction.localWarmupWordBudget M B) 1 + 1 ≤
      X ^ preparedWarmupBitDegree := by
  let D := max representativeShellDegree (max physicalShellDegree preparedCacheReturnBitDegree)
  have hpos : 0 < X := by omega
  have hr := (localRepresentativesBitBudget_fixedPower P F B X hX hP hF (by omega)).trans
    (Nat.pow_le_pow_right hpos (show representativeShellDegree ≤ D from Nat.le_max_left _ _))
  have hc := (physicalContinuationBitBudget_fixedPower M P _ 0 0 (B + 4) X hX hM hP hrep
    (Nat.zero_le _) (Nat.zero_le _) hB hV hCartesian).trans
      (Nat.pow_le_pow_right hpos (show physicalShellDegree ≤ D from
        (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
  have hret := (preparedCacheReturnBitBudget_fixedPower M B 0 1 X hX hM (by omega)
    (Nat.zero_le _) (by omega)).trans
      (Nat.pow_le_pow_right hpos (show preparedCacheReturnBitDegree ≤ D from
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hreturn : BinaryFraction.powerDenominatorBitBudget 0 (BinaryFraction.localWarmupWordBudget M B) 1 ≤
      X ^ D := by
    apply le_trans _ hret
    unfold BinaryFraction.powerDenominatorBitBudget
    gcongr
    exact warmup_width_le_continuation M B
  have hw := warmup_le_continuation M P F B
  have hone : 1 ≤ X ^ D := Nat.succ_le_of_lt (pow_pos hpos D)
  have he : 8 ≤ X ^ 3 := (show 8 = (2 : ℕ) ^ 3 by decide).trans_le (Nat.pow_le_pow_left hX 3)
  calc
    _ ≤ 3 * X ^ D + 4 := by omega
    _ ≤ 8 * X ^ D := by omega
    _ ≤ X ^ 3 * X ^ D := Nat.mul_le_mul_right _ he
    _ = X ^ preparedWarmupBitDegree := by
      rw [← pow_add]
      change X ^ (3 + D) = X ^ (D + 3)
      rw [Nat.add_comm 3 D]

end EditApproximation

end OAI
