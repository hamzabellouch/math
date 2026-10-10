import OAI.Combinatorics.EditApproximation.Refinement.ComputedLocalKernelWork

namespace OAI

namespace EditApproximation

/-- Enlarge the exponent of the common computed kernel scale. -/
theorem computedLocalKernelBudget_mono (N D E : ℕ) (h : D ≤ E) :
    computedLocalKernelBudget D N ≤ computedLocalKernelBudget E N := by
  unfold computedLocalKernelBudget localKernelPowerExponent
  apply Nat.pow_le_pow_right (Nat.two_pow_pos _)
  exact Nat.mul_le_mul_left _ h

theorem computedLocalKernelBudget_three (N D x y z : ℕ) (hH : 3 ≤ inputHeight N)
    (hx : x ≤ computedLocalKernelBudget D N) (hy : y ≤ computedLocalKernelBudget D N)
    (hz : z ≤ computedLocalKernelBudget D N) :
    x + y + z ≤ computedLocalKernelBudget (D + 1) N := by
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := inputHeight N ^ L
  have hL : 1 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hHS : inputHeight N ≤ S := Nat.le_pow hL
  have hx' : x ≤ S ^ D := by simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using hx
  have hy' : y ≤ S ^ D := by simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using hy
  have hz' : z ≤ S ^ D := by simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using hz
  have hsum : x + y + z ≤ 3 * S ^ D := by omega
  have h3S : 3 ≤ S := hH.trans hHS
  calc
    _ ≤ 3 * S ^ D := hsum
    _ ≤ S * S ^ D := Nat.mul_le_mul_right _ h3S
    _ = S ^ (D + 1) := (pow_succ' S D).symm
    _ = _ := by simp only [S, ← pow_mul]; rfl

/-- The fixed guard overhead at the eight-power word bound. -/
theorem computed_kernel_guard_cost (N : ℕ) (hH : 64 ≤ inputHeight N) :
    50 * inputHeight N ^ 8 + 100 ≤ computedLocalKernelBudget 1 N := by
  let H := inputHeight N
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  have hL : 10 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hpow : 50 * H ^ 8 + 100 ≤ H ^ 10 := by
    have hone : 1 ≤ H ^ 8 := one_le_pow₀ (by omega)
    have hcoef : 150 ≤ H ^ 2 := by nlinarith only [hH]
    calc
      _ ≤ 150 * H ^ 8 := by omega
      _ ≤ H ^ 2 * H ^ 8 := Nat.mul_le_mul_right _ hcoef
      _ = _ := by rw [← pow_add]
  apply hpow.trans
  change H ^ 10 ≤ H ^ (L * 1)
  simpa only [Nat.mul_one] using Nat.pow_le_pow_right (by omega : 0 < H) hL

end EditApproximation

end OAI
