import OAI.Combinatorics.EditApproximation.Queries.QuerySourceWork
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSourceCost
import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineKeyCost
import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineRangeCost
import OAI.Combinatorics.EditApproximation.Queries.QueryScopedSourceCost

namespace OAI

namespace EditApproximation

private theorem source_read_sum_bound {κ : Type*} (keys : List κ) (cost : κ → ℕ) (B : ℕ)
    (h : ∀ key ∈ keys, cost key ≤ B) : (keys.map cost).sum ≤ keys.length * B := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have hh := h key List.mem_cons_self
    have ht := ih (fun k hk => h k (List.mem_cons_of_mem key hk))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

namespace BinaryFraction

def queryGroupGatherBitBudget (M F exponent eM eF B Rp W K : ℕ) : ℕ :=
  Rp + queryGroupSourceKeysBitBudget M F exponent eM eF B +
    queryGroupSourceKeysLength M F exponent eM eF B * (W + 3) + K

def queryOnlineGatherBitBudget (M P B Rp R W K : ℕ) : ℕ :=
  Rp + queryOnlineKeysBitBudget B +
    (B + 1) * (queryOnlineRangeBitBudget M P (B + 1) R + W + 3) + K

end BinaryFraction

open BinaryFraction

theorem queryGroupSourceGather_work_bound {ι β : Type*} {n : ℕ}
    (M N F Q exponent eM eF B Rp W K : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ) (q : TargetInterval n)
    (reader : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (next : List (GroupScalarKey M F Q) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hFb : Nat.size F + 2 ≤ B)
    (hMb : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B) (hes : eM + eF + 7 ≤ B)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B) (ha : a.width ≤ B)
    (hv : (initial q).1.width ≤ B) (hw : 0 ≤ (initial q).1.value) (hp : (initial q).2 ≤ Rp)
    (hr : ∀ key ∈ (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (initial q).1 q).1,
      (reader key).work oracle readWork ≤ W)
    (hnext :
      let keys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (initial q).1 q).1
      (next keys (keys.map fun key => (reader key).value oracle)).work oracle readWork ≤ K) :
    (queryGroupSourceGather M N F Q exponent eM eF hM hF a initial q reader next).work oracle readWork ≤
      queryGroupGatherBitBudget M F exponent eM eF B Rp W K := by
  let keys := queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (initial q).1 q
  have hk := queryGroupSourceKeysWithWork_bounds M N F Q exponent eM eF B hM hF a (initial q).1 q
    hB hN hFb hMb hQ hes he hn ha hv hw
  have hs := (source_read_sum_bound keys.1 (fun key => (reader key).work oracle readWork + 3) (W + 3)
    (fun key hkey => Nat.add_le_add_right (hr key hkey) 3)).trans (Nat.mul_le_mul_right _ hk.1)
  change (next keys.1 (keys.1.map fun key => (reader key).value oracle)).work oracle readWork ≤ K at hnext
  have hkc : keys.2 ≤ queryGroupSourceKeysBitBudget M F exponent eM eF B := hk.2
  rw [queryGroupSourceGather_work]
  change (initial q).2 + keys.2 + (keys.1.map fun key => (reader key).work oracle readWork + 3).sum +
    (next keys.1 (keys.1.map fun key => (reader key).value oracle)).work oracle readWork ≤ _
  unfold queryGroupGatherBitBudget
  omega

theorem queryOnlineSourceGather_work_bound {ι β α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H B Rp R W K : ℕ) (hP : 0 < P)
    (tau a : BinaryFraction) (initial : TargetInterval target.length → BinaryFraction × ℕ)
    (child : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (q : TargetInterval target.length)
    (reader : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
    (next : List (ℕ × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hFb : Nat.size F + 2 ≤ B) (hF : 1 ≤ F)
    (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B) (he : exponent + 1 ≤ B)
    (hnx : Nat.size source.length ≤ B) (hny : Nat.size target.length ≤ B)
    (hH : Nat.size H ≤ B) (hd : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B) (hv : (initial q).1.width ≤ B)
    (hp : (initial q).2 ≤ Rp) (hc : ∀ i r, (child i r).1.width ≤ B)
    (hR : ∀ i r, (child i r).2 ≤ R)
    (hr : ∀ key ∈ (queryOnlineKeysWithWork N P F hP a (initial q).1 q).1,
      (reader key (queryOnlineRangeWithWork parent P exponent H tau child key).1).work oracle readWork ≤ W)
    (hnext :
      let keys := (queryOnlineKeysWithWork N P F hP a (initial q).1 q).1
      (next keys (keys.map fun key =>
        (reader key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle)).work oracle readWork ≤ K) :
    (queryOnlineSourceGather parent N P F exponent H hP tau a initial child q reader next).work oracle readWork ≤
      queryOnlineGatherBitBudget M P B Rp R W K := by
  let keys := queryOnlineKeysWithWork N P F hP a (initial q).1 q
  let range := queryOnlineRangeWithWork parent P exponent H tau child
  have hk := queryOnlineKeysWithWork_bounds N P F B hP a (initial q).1 q hB hN hFb hF hPb hny ha hv
  have hs := source_read_sum_bound keys.1
    (fun key => (range key).2 + (reader key (range key).1).work oracle readWork + 3)
    (queryOnlineRangeBitBudget M P (B + 1) R + W + 3) (by
      intro key hkey
      have hb := queryOnlineKeysWithWork_scale N P F B hP a (initial q).1 q hN hF key hkey
      have hc' := (queryOnlineRangeWithWork_bounds source target parent P exponent H (B + 1) R hP tau child key
        (by omega) (by omega) (by omega) (by omega) hb (by omega) (by omega) (by omega) (by omega)
        (htau.trans (by omega)) (fun i r => (hc i r).trans (by omega)) hR).2
      have hread := hr key hkey
      change (range key).2 ≤ queryOnlineRangeBitBudget M P (B + 1) R at hc'
      change (reader key (range key).1).work oracle readWork ≤ W at hread
      omega)
  have hs' := hs.trans (Nat.mul_le_mul_right _ hk.1)
  have hkc : keys.2 ≤ queryOnlineKeysBitBudget B := hk.2
  change (next keys.1 (keys.1.map fun key => (reader key (range key).1).value oracle)).work oracle readWork ≤ K at hnext
  rw [queryOnlineSourceGather_work]
  change (initial q).2 + keys.2 +
    (keys.1.map fun key => (range key).2 + (reader key (range key).1).work oracle readWork + 3).sum +
    (next keys.1 (keys.1.map fun key => (reader key (range key).1).value oracle)).work oracle readWork ≤ _
  unfold queryOnlineGatherBitBudget
  omega

end EditApproximation

end OAI
