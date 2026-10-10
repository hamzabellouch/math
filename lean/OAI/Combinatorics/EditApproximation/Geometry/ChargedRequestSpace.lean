import OAI.Combinatorics.EditApproximation.Geometry.ChargedGlobalQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRequestBits
import OAI.Combinatorics.EditApproximation.Binary.BinaryMemoSpace

namespace OAI

/-! A polynomial retained-cache bound for every execution. The estimate
uses only fixed-width key insertion and computed parameter sizes, and
therefore does not depend on an approximation success event. -/

namespace EditApproximation

theorem computed_charged_request_bits_le (N nx ny passes copies : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hpasses : passes ≤ inputHeight N ^ 2) (hcopies : copies ≤ inputHeight N ^ 2) :
    ChargedPhysicalRequest.bits (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S ≤ 11 * inputHeight N + 3 := by
  let H := inputHeight N
  have hentry := computed_entryCapacity_bound N nx ny hN hell hnx hny
  have hbits := computed_request_bits_le N nx ny passes copies hN hell hnx hny hpasses hcopies
  have htable : PhysicalTableRequest.capacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S + 1 ≤ 2 ^ (11 * H + 1) := by
    exact (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mp hbits
  have hentry' : PhysicalTableRequest.entryCapacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny ≤ 2 ^ (11 * H + 1) :=
    hentry.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega))
  unfold ChargedPhysicalRequest.bits
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2
  unfold ChargedPhysicalRequest.capacity
  have hp : 2 ^ (11 * H + 3) = 4 * 2 ^ (11 * H + 1) := by
    rw [show 11 * H + 3 = (11 * H + 1) + 2 by omega, pow_add]
    norm_num
    omega
  change 2 * (_ + _) + 1 ≤ 2 ^ (11 * H + 3)
  rw [hp]
  omega

theorem two_pow_inputHeight_le (N : ℕ) : 2 ^ inputHeight N ≤ 4 * (N + 2) ^ 2 := by
  have hc : 0 < Nat.clog 2 (N + 2) :=
    Nat.clog_pos (by decide : 1 < (2 : ℕ)) (by omega)
  have hH := (rejectionWord_range (Nat.clog 2 (N + 2)) hc).2
  have hN := (rejectionWord_range (N + 2) (by omega)).2
  change inputHeight N < 2 * Nat.clog 2 (N + 2) at hH
  change 2 ^ Nat.clog 2 (N + 2) < 2 * (N + 2) at hN
  calc
    _ ≤ 2 ^ (2 * Nat.clog 2 (N + 2)) := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hH.le
    _ = (2 ^ Nat.clog 2 (N + 2)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    _ ≤ (2 * (N + 2)) ^ 2 := Nat.pow_le_pow_left hN.le 2
    _ = _ := by ring

theorem computed_charged_cache_nodes {κ : Type*} (N nx ny passes copies : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hpasses : passes ≤ inputHeight N ^ 2) (hcopies : copies ≤ inputHeight N ^ 2)
    (rank : κ → ℕ) (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (encode : κ → ℕ) (key : κ) :
    (rankedMemoEvaluate rank program
      (ChargedPhysicalRequest.bits (integerParameters N).M
        (intervalTreeDepth (integerParameters N).M nx) ny passes copies
        (integerParameters N).T (integerParameters N).S) encode key .empty).memory.nodes + 1 ≤
      (N + 2) ^ 48 := by
  have hbits := computed_charged_request_bits_le N nx ny passes copies hN hell hnx hny hpasses hcopies
  have hcache := rankedMemoEvaluate_nodes_bound rank program
    (ChargedPhysicalRequest.bits (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S) encode key
  have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.add_le_add_right hbits 1)
  apply (hcache.trans hpow).trans
  calc
    2 ^ (11 * inputHeight N + 3 + 1) = 16 * (2 ^ inputHeight N) ^ 11 := by
      rw [show 11 * inputHeight N + 3 + 1 = inputHeight N * 11 + 4 by omega, pow_add, pow_mul]
      norm_num
      omega
    _ ≤ 16 * (4 * (N + 2) ^ 2) ^ 11 := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (two_pow_inputHeight_le N) 11)
    _ = 2 ^ 26 * (N + 2) ^ 22 := by ring
    _ ≤ (N + 2) ^ 26 * (N + 2) ^ 22 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 26)
    _ = (N + 2) ^ 48 := by rw [← pow_add]

end EditApproximation

end OAI
