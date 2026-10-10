import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRequestEncoding
import OAI.Combinatorics.EditApproximation.Refinement.ComputedEarlierInputBudget

namespace OAI

/-! The cache key width is linear in the input height, once the actual
pass and copy bounds are substituted. The numerical capacity is only a
bound: no array of that capacity is allocated. -/

namespace EditApproximation

theorem computed_entryCapacity_bound (N nx ny : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N) :
    PhysicalTableRequest.entryCapacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny ≤ 2 ^ (5 * inputHeight N) := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let J := intervalTreeDepth M nx
  have hM : M ≤ H := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)
  have hMH : M ≤ 2 ^ H := hM.trans (Nat.lt_two_pow_self.le)
  have hnx' : max 1 nx ≤ 2 ^ H := max_le Nat.one_le_two_pow
    (hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N)))
  have htree : M ^ J ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ M * max 1 nx := intervalTreeDepth_power_le M nx (computed_branching_bounds N hN hell).1
      _ ≤ 2 ^ H * 2 ^ H := Nat.mul_le_mul hMH hnx'
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hJ : J ≤ H := by
    have hj := computed_tree_depth_bound N nx hN hnx hell
    change J * inputSmallLog N ≤ 100 * H at hj
    nlinarith only [hj, hell]
  have hJ' : J + 1 ≤ 2 ^ H := (Nat.add_le_add_right hJ 1).trans (Nat.lt_two_pow_self)
  have hny' : ny + 1 ≤ 2 ^ H := (by omega : ny + 1 ≤ N + 2).trans (inputHeight_covers_length N)
  unfold PhysicalTableRequest.entryCapacity
  calc
    (ny + 1) ^ 2 * (M ^ J * (J + 1)) ≤ (2 ^ H) ^ 2 * (2 ^ (2 * H) * 2 ^ H) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hny' 2) (Nat.mul_le_mul htree hJ')
    _ = 2 ^ (5 * H) := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega

theorem computed_request_bits_le (N nx ny passes copies : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hpasses : passes ≤ inputHeight N ^ 2) (hcopies : copies ≤ inputHeight N ^ 2) :
    PhysicalTableRequest.bits (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S ≤ 11 * inputHeight N + 1 := by
  let H := inputHeight N
  have hH : 4 ≤ H := (by omega : 4 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hHpow : H ^ 2 ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ (2 ^ H) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hstride := (computed_history_budget_le_height_sq N hH).trans hHpow
  have hentry := computed_entryCapacity_bound N nx ny hN hell hnx hny
  have hcapacity : PhysicalTableRequest.capacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S ≤ 2 ^ (11 * H) := by
    unfold PhysicalTableRequest.capacity
    calc
      _ ≤ 2 ^ (2 * H) * (2 ^ (2 * H) * (2 ^ (5 * H) * 2 ^ (2 * H))) :=
        Nat.mul_le_mul hstride
          (Nat.mul_le_mul (hcopies.trans hHpow) (Nat.mul_le_mul hentry (hpasses.trans hHpow)))
      _ = _ := by rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  unfold PhysicalTableRequest.bits
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
  calc
    _ ≤ 2 ^ (11 * H) + 2 ^ (11 * H) := Nat.add_le_add hcapacity Nat.one_le_two_pow
    _ = _ := by
      change 2 ^ (11 * H) + 2 ^ (11 * H) = 2 ^ (11 * H + 1)
      rw [pow_succ]
      omega

end EditApproximation

end OAI
