import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSupportCost
import OAI.Combinatorics.EditApproximation.Queries.QueryBandInputCost
import OAI.Combinatorics.EditApproximation.Queries.QueryBandGather

namespace OAI

namespace EditApproximation

private theorem outer_read_sum_bound {κ : Type*} (keys : List κ) (cost : κ → ℕ) (B : ℕ)
    (h : ∀ key ∈ keys, cost key ≤ B) : (keys.map cost).sum ≤ keys.length * B := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have hh := h key List.mem_cons_self
    have ht := ih (fun k hk => h k (List.mem_cons_of_mem key hk))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

namespace BinaryFraction

def queryInitialGatherBitBudget (P F exponent B R K : ℕ) : ℕ :=
  R + queryInitialSupportBitBudget P F exponent B + queryInitialSupportLength P F exponent B * (R + 3) + K

def queryBandGatherBitBudget (M P F exponent B Rp W K : ℕ) : ℕ :=
  queryBandInputsBitBudget M P F exponent B Rp +
    2 * (queryEarlierRepresentativesLength P F exponent B * (M * (40 * P + 2) ^ 2) * (W + 3)) + K

end BinaryFraction
open BinaryFraction

theorem queryInitialGather_work_bound {ι β : Type*} {n : ℕ}
    (N P F exponent B R K : ℕ) (hP : 0 < P) (a : BinaryFraction) (q : TargetInterval n)
    (reader : TargetInterval n → BitQuery ι BinaryFraction)
    (next : List (TargetInterval n) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B) (he : exponent + 1 ≤ B) (ha : a.width ≤ B)
    (hv : ((reader q).value oracle).width ≤ B) (hw : 0 ≤ ((reader q).value oracle).value)
    (hPd : ∃ e : ℕ, P = 2 ^ e) (hR : ∀ r, (reader r).work oracle readWork ≤ R)
    (hnext :
      let keys := (queryInitialSupportWithWork N P F exponent hP a ((reader q).value oracle) q).1
      (next keys (keys.map fun r => (reader r).value oracle)).work oracle readWork ≤ K) :
    (queryInitialGather N P F exponent hP a q reader next).work oracle readWork ≤
      queryInitialGatherBitBudget P F exponent B R K := by
  let support := queryInitialSupportWithWork N P F exponent hP a ((reader q).value oracle) q
  have hs := queryInitialSupportWithWork_bounds N P F exponent B hP a ((reader q).value oracle) q
    hB hN hF hFpos hPb hn he ha hv hw hPd
  have hr := (outer_read_sum_bound support.1 (fun r => (reader r).work oracle readWork + 3) (R + 3)
    (fun r _ => Nat.add_le_add_right (hR r) 3)).trans (Nat.mul_le_mul_right _ hs.1)
  have hsc : support.2 ≤ queryInitialSupportBitBudget P F exponent B := hs.2
  change (next support.1 (support.1.map fun r => (reader r).value oracle)).work oracle readWork ≤ K at hnext
  rw [queryInitialGather_work]
  change (reader q).work oracle readWork + support.2 +
    (support.1.map fun r => (reader r).work oracle readWork + 3).sum +
    (next support.1 (support.1.map fun r => (reader r).value oracle)).work oracle readWork ≤ _
  have hq := hR q
  unfold queryInitialGatherBitBudget
  omega

theorem queryBandGather_work_bound {ι β : Type*} {nx ny : ℕ}
    (M N P F exponent B Rp W K : ℕ) (parent : TargetInterval nx) (hP : 0 < P)
    (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (massReader initialReader : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (next : List (Fin M × TargetInterval ny) → List BinaryFraction → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B) (hM : Nat.size M ≤ B)
    (he : exponent + 1 ≤ B) (ha : a.width ≤ B) (hi : ∀ r, (initial r).1.width ≤ B)
    (hR : ∀ r, (initial r).2 ≤ Rp) (hw : 0 ≤ (initial q).1.value) (hPd : ∃ e : ℕ, P = 2 ^ e)
    (hm : ∀ key, (massReader key).work oracle readWork ≤ W)
    (hr : ∀ key, (initialReader key).work oracle readWork ≤ W)
    (hnext :
      let keys := (queryBandInputsWithWork M parent N P F exponent hP a initial q).1
      (next keys (keys.map fun key => (massReader key).value oracle)
        (keys.map fun key => (initialReader key).value oracle)).work oracle readWork ≤ K) :
    (queryBandGather M parent N P F exponent hP a initial q massReader initialReader next).work oracle readWork ≤
      queryBandGatherBitBudget M P F exponent B Rp W K := by
  let keys := queryBandInputsWithWork M parent N P F exponent hP a initial q
  have hk := queryBandInputsWithWork_bounds M N P F exponent B Rp parent hP a initial q
    hB hN hF hFpos hPb hnx hny hM he ha hi hR hw hPd
  have hmass := (outer_read_sum_bound keys.1 (fun key => (massReader key).work oracle readWork + 3)
    (W + 3) (fun key _ => Nat.add_le_add_right (hm key) 3)).trans (Nat.mul_le_mul_right _ hk.1)
  have hinit := (outer_read_sum_bound keys.1 (fun key => (initialReader key).work oracle readWork + 3)
    (W + 3) (fun key _ => Nat.add_le_add_right (hr key) 3)).trans (Nat.mul_le_mul_right _ hk.1)
  have hkc : keys.2 ≤ queryBandInputsBitBudget M P F exponent B Rp := hk.2
  change (next keys.1 (keys.1.map fun key => (massReader key).value oracle)
    (keys.1.map fun key => (initialReader key).value oracle)).work oracle readWork ≤ K at hnext
  rw [queryBandGather_work]
  change keys.2 + (keys.1.map fun key => (massReader key).work oracle readWork + 3).sum +
    (keys.1.map fun key => (initialReader key).work oracle readWork + 3).sum +
    (next keys.1 (keys.1.map fun key => (massReader key).value oracle)
      (keys.1.map fun key => (initialReader key).value oracle)).work oracle readWork ≤ _
  unfold queryBandGatherBitBudget
  omega

end EditApproximation

end OAI
