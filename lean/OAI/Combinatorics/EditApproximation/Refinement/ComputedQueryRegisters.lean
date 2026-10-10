import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryWidth
import OAI.Combinatorics.EditApproximation.Refinement.ComputedPreparedWords
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryBudgetAlgebra

namespace OAI

namespace EditApproximation
open BinaryFraction

/-- The remaining scalar premises of the concrete table dispatcher. -/
structure ComputedQueryRegisters (N ny J : ℕ)
    (request : PhysicalTableRequest (integerParameters N).M J ny) : Prop where
  targetSuccessor : Nat.size (ny + 1) + 2 ≤ inputHeight N ^ 8
  initial : Nat.size ((32 * inputSmallLog N + 1) * N) + 3 ≤ inputHeight N ^ 8
  depth : Nat.size J ≤ inputHeight N ^ 8
  index : Nat.size request.index ≤ inputHeight N ^ 8
  warmup : Nat.size (integerParameters N).T ≤ inputHeight N ^ 8
  refinement : Nat.size (integerParameters N).S ≤ inputHeight N ^ 8
  rank : Nat.size (request.combinedRank (integerParameters N).T (integerParameters N).S) ≤ inputHeight N ^ 8
  pass : Nat.size request.pass ≤ inputHeight N ^ 8
  copy : Nat.size request.copy ≤ inputHeight N ^ 8
  passes : Nat.size (computedSeedPassCount N + 1) ≤ inputHeight N ^ 8
  copies : Nat.size (inputHeight N ^ 2 + 1) ≤ inputHeight N ^ 8
  multiplier : Nat.size (scheduledSeedMultiplier N (request.pass - 1)) + 2 ≤ inputHeight N ^ 8
  mean : warmupAverageWordBudget (integerParameters N).T (inputHeight N ^ 3) ≤ inputHeight N ^ 8

/-- None of these register bounds assumes a successful random draw. -/
theorem computedQueryRegisters (N ny J : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) (hny : ny ≤ N) (hJ : J ≤ inputHeight N)
    (request : PhysicalTableRequest (integerParameters N).M J ny)
    (hr : request.Bounded (computedSeedPassCount N + 1) (inputHeight N ^ 2)
      (integerParameters N).T (integerParameters N).S) : ComputedQueryRegisters N ny J request := by
  let H := inputHeight N
  have hH : 64 ≤ H := (two_hundred_le_two_pow_thousand.trans hell |>.trans' (by decide : 64 ≤ 200)).trans
    (computed_smallLog_le_height N)
  have hp : 0 < H := by omega
  have h1 : 1 ≤ H := by omega
  have h28 : H ^ 2 ≤ H ^ 8 := Nat.pow_le_pow_right hp (by decide)
  have h38 : H ^ 3 ≤ H ^ 8 := Nat.pow_le_pow_right hp (by decide)
  have h48 : H ^ 4 ≤ H ^ 8 := Nat.pow_le_pow_right hp (by decide)
  have hH8 : H ≤ H ^ 8 := Nat.le_pow (by decide)
  have hhist : (integerParameters N).T + (integerParameters N).S + 1 ≤ H ^ 2 :=
    computed_history_budget_le_height_sq N (by omega)
  have hT : (integerParameters N).T ≤ H ^ 2 := by omega
  have hS : (integerParameters N).S ≤ H ^ 2 := by omega
  have hindex : request.index ≤ H ^ 2 := hr.2.2.trans (by omega)
  have hpasses : computedSeedPassCount N ≤ H := computedSeedPassCount_le_height N hN hell
  have hpass : request.pass ≤ H := (Nat.le_of_lt_succ hr.1).trans hpasses
  have hcopy : request.copy ≤ H ^ 2 := hr.2.1.le
  have hsize : Nat.size N ≤ H := computed_input_size_le_height N
  have hsmall : Nat.size (inputSmallLog N) ≤ H :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
  have hinit : Nat.size ((32 * inputSmallLog N + 1) * N) + 3 ≤ H ^ 2 := by
    have h1 := natural_product_bit_length 32 (inputSmallLog N)
    have h2 := natural_sum_bit_length (32 * inputSmallLog N) 1
    have h3 := natural_product_bit_length (32 * inputSmallLog N + 1) N
    have h32 : Nat.size 32 = 6 := by decide
    simp only [h32, Nat.size_one] at h1 h2
    have hpoly : 2 * H + 11 ≤ H ^ 2 := by nlinarith only [hH]
    omega
  have htarget : Nat.size (ny + 1) + 2 ≤ H ^ 2 := by
    have hs := natural_sum_bit_length ny 1
    have hn := (Nat.size_le_size hny).trans hsize
    simp only [Nat.size_one] at hs
    have hpoly : H + 4 ≤ H ^ 2 := by nlinarith only [hH]
    omega
  have hrank : request.combinedRank (integerParameters N).T (integerParameters N).S ≤ H ^ 4 := by
    have hm := Nat.mul_le_mul hpass hhist
    have hd : request.remainingDepth ≤ H := (Nat.sub_le _ _).trans hJ
    have hc : H + H * H ^ 2 + H ^ 2 ≤ H ^ 4 := by
      have h2 : 3 * H ≤ H ^ 2 := by nlinarith only [hH]
      have h3 : H ≤ H ^ 2 := Nat.le_pow (by decide)
      have h4 : H * H ^ 2 ≤ H ^ 4 := by
        exact (Nat.mul_le_mul_right (H ^ 2) h3).trans_eq (by ring)
      nlinarith only [hH, h2, h3, h4, sq_nonneg (H * (H - 2))]
    unfold PhysicalTableRequest.combinedRank PhysicalTableRequest.rank
    omega
  have hmult : Nat.size (scheduledSeedMultiplier N (request.pass - 1)) + 2 ≤ H ^ 3 := by
    unfold scheduledSeedMultiplier
    rw [Nat.size_pow]
    have hd : dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N)
        (request.pass - 1) ≤ computedSeedInitialExponent N := Nat.sub_le _ _
    have hw := computed_window_le_height_cube N hN (by omega) (by omega)
    change computedSeedInitialExponent N + 8 ≤ H ^ 3 at hw
    omega
  have hmean : warmupAverageWordBudget (integerParameters N).T (H ^ 3) ≤ H ^ 8 := by
    have hts : Nat.size (integerParameters N).T ≤ H ^ 2 :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans hT
    have hm := Nat.mul_le_mul_right (H ^ 3 + 1) hT
    have h5 : H ^ 2 * (H ^ 3 + 1) = H ^ 5 + H ^ 2 := by ring
    rw [h5] at hm
    have h25 : H ^ 2 ≤ H ^ 5 := Nat.pow_le_pow_right hp (by decide)
    have h35 : H ^ 3 ≤ H ^ 5 := Nat.pow_le_pow_right hp (by decide)
    have hu : 1 ≤ H ^ 5 := one_le_pow₀ h1
    have hcoeff : 50 ≤ H ^ 3 := (by omega : 50 ≤ H).trans (Nat.le_pow (by decide))
    have h58 : 50 * H ^ 5 ≤ H ^ 8 :=
      (Nat.mul_le_mul_right (H ^ 5) hcoeff).trans_eq (by ring)
    unfold warmupAverageWordBudget bandMassTotalStorageBudget
    nlinarith only [hts, hm, h25, h35, hu, h58]
  refine ⟨htarget.trans h28, hinit.trans h28,
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hJ).trans hH8,
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hindex).trans h28,
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hT).trans h28,
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hS).trans h28,
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hrank).trans h48,
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hpass).trans hH8,
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hcopy).trans h28,
    ?_, ?_, hmult.trans h38, hmean⟩
  · have hbound : computedSeedPassCount N + 1 ≤ H ^ 2 := by nlinarith only [hpasses, hH]
    exact ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hbound).trans h28
  · have hbound : H ^ 2 + 1 ≤ H ^ 3 := by
      have hs := Nat.mul_le_mul_right (H ^ 2) (by omega : 2 ≤ H)
      rw [← pow_succ'] at hs
      change 2 * H ^ 2 ≤ H ^ 3 at hs
      have hu : 1 ≤ H ^ 2 := one_le_pow₀ h1
      omega
    exact ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hbound).trans h38

end EditApproximation

end OAI
