import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryMemo
import OAI.Combinatorics.EditApproximation.Geometry.HeightPowerWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter

/- One materialized row of the shared pass-parameter array. -/


/-- All pass constants and the normalization base are constructed before evaluation. -/


theorem computedQuerySetupWithWork_pass (N : ℕ) (pass : Fin (computedSeedPassCount N + 1)) :
    ((computedQuerySetupWithWork N).1.1.get pass) =
      ((scheduledSeedWordWithWork N pass.val).1, computedQueryParameters N pass.val) := by
  simp only [computedQuerySetupWithWork, vectorMapWithWork_value, computedQueryPassWithWork,
    computedQueryParameters]

theorem computedQuerySetupWithWork_base (N : ℕ) :
    (computedQuerySetupWithWork N).1.2 = computedQueryBase N := by
  simp only [computedQuerySetupWithWork, computedQueryBase]

theorem computedQuerySetupWithWork_cost (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (computedQuerySetupWithWork N).2 ≤ inputHeight N ^ 12 := by
  let H := inputHeight N
  have hH : 64 ≤ H := (by have := two_hundred_le_two_pow_thousand.trans hell; omega :
    64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hp : 0 < H := by omega
  have hword : (inputSmallLog N).bits.length ≤ Nat.size (inputSmallLog N) := by
    rw [← Nat.size_eq_bits_len]
  have hwidth : (inputSmallLog N).bits.length ≤ H := hword.trans
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N))
  have hpass : computedSeedPassCount N + 1 ≤ H ^ 2 := by
    have h := computedSeedPassCount_le_height N hN hell
    change computedSeedPassCount N ≤ H at h
    nlinarith only [h, hH]
  have h3 : H ^ 3 ≤ H ^ 9 := Nat.pow_le_pow_right hp (by decide)
  have hu : 1 ≤ H ^ 9 := one_le_pow₀ (by omega)
  have hc (pass : Fin (computedSeedPassCount N + 1)) :
      (computedQueryPassWithWork N pass.val).2 ≤ 4 * H ^ 9 := by
    have hs := (scheduledSeedWordWithWork_bounds N pass.val hN (by omega) hH).2
    have hw := refinementParameterWordsWithWork_cost N pass.val (inputSmallLog N).bits
      (by rw [bitWordValue_bits]; exact Nat.two_pow_pos _) hword hH
    change _ ≤ H ^ 3 at hs
    change _ ≤ H ^ 9 at hw
    unfold computedQueryPassWithWork
    dsimp only
    omega
  have hv := BinaryFraction.vectorMapWithWork_cost_le (computedSeedPassCount N + 1)
    (fun i => computedQueryPassWithWork N i.val) (4 * H ^ 9) hc
  have hvc : (vectorMapWithWork (computedSeedPassCount N + 1)
      (fun i => computedQueryPassWithWork N i.val)).2 ≤ 5 * H ^ 11 := by
    have hmul := Nat.mul_le_mul_right (4 * H ^ 9 + 6) hpass
    have h2 : H ^ 2 ≤ H ^ 11 := Nat.pow_le_pow_right hp (by decide)
    have hprod : H ^ 2 * (4 * H ^ 9 + 6) = 4 * H ^ 11 + 6 * H ^ 2 := by ring
    have hH2 : H ^ 2 * 6 ≤ H ^ 11 := by
      have hcoef : 6 ≤ H ^ 9 := (by omega : 6 ≤ H).trans (Nat.le_pow (by decide))
      exact (Nat.mul_le_mul_left (H ^ 2) hcoef).trans_eq (by ring)
    rw [hprod] at hmul
    omega
  have hb := refinementBaseWithWork_cost (inputSmallLog N).bits H hwidth
  have hbc : (refinementBaseWithWork (inputSmallLog N).bits).2 ≤ H ^ 8 := by
    have hlinear : 11 * (H + 1) + 1 ≤ 12 * H := by omega
    have hs := Nat.pow_le_pow_left hlinear 2
    have hpoly : bitPowerBitBudget 10 H + 200 * (H + 1) ≤ 400000 * H ^ 2 := by
      unfold bitPowerBitBudget
      nlinarith only [hs, hH]
    have hcoef : 400000 ≤ H ^ 6 :=
      (by norm_num : 400000 ≤ (64 : ℕ) ^ 6).trans (Nat.pow_le_pow_left hH 6)
    exact hb.trans (hpoly.trans ((Nat.mul_le_mul_right (H ^ 2) hcoef).trans_eq (by ring)))
  have h811 : H ^ 8 ≤ H ^ 11 := Nat.pow_le_pow_right hp (by decide)
  have hu11 : 1 ≤ H ^ 11 := one_le_pow₀ (by omega)
  have hfinal : 11 * H ^ 11 ≤ H ^ 12 :=
    (Nat.mul_le_mul_right (H ^ 11) (by omega : 11 ≤ H)).trans_eq (by ring)
  change (vectorMapWithWork (computedSeedPassCount N + 1)
    (fun i => computedQueryPassWithWork N i.val)).2 +
    (refinementBaseWithWork (inputSmallLog N).bits).2 + 5 ≤ H ^ 12
  omega

end EditApproximation

end OAI
