import OAI.Combinatorics.EditApproximation.Queries.QueryRawCenterCost
import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedWork

namespace OAI

namespace EditApproximation.BinaryFraction

def queryOnlineKeysBitBudget (B : ℕ) : ℕ :=
  queryScalesBitBudget B + (B + 1) * (600 * (B + 3) ^ 2 + 6) + 1

theorem queryOnlineKeysWithWork_bounds {n : ℕ} (N P F B : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B)
    (ha : a.width ≤ B) (hv : value.width ≤ B) :
    (queryOnlineKeysWithWork N P F hP a value q).1.length ≤ B + 1 ∧
    (queryOnlineKeysWithWork N P F hP a value q).2 ≤ queryOnlineKeysBitBudget B := by
  let scales := queryScalesWithWork N F a value
  let run := fun b =>
    let spacing := seedGridSpacingWithWork b P
    let center := roundStateWithWork (bitWordValue spacing.1) (seedGridSpacingWithWork_pos b P hP) q
    ((b, center.1), spacing.2 + center.2 + 2)
  have hs := queryScalesWithWork_bounds N F B a value hB hN hF ha hv
  have hc (b : ℕ) (hb : b ∈ scales.1) : (run b).2 ≤ 600 * (B + 3) ^ 2 + 3 := by
    have hm := queryScalesWithWork_member N F B a value hN hFpos b hb
    have hsp := seedGridSpacingWithWork_bounds b P (B + 1) hm.1 (by omega)
    have hsize : Nat.size (bitWordValue (seedGridSpacingWithWork b P).1) ≤ B + 2 :=
      (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans hsp.1
    have hr := roundStateWithWork_cost (bitWordValue (seedGridSpacingWithWork b P).1)
      (seedGridSpacingWithWork_pos b P hP) q (B + 2) hsize (by omega)
    have hspc := hsp.2
    dsimp only [run]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hspc hr
    omega
  have hm := (arithmeticMapWithWork_cost run scales.1 (600 * (B + 3) ^ 2 + 3) hc).trans
    (Nat.mul_le_mul_right _ hs.1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hm
  constructor
  · simpa only [queryOnlineKeysWithWork, arithmeticMapWithWork_value, List.length_map] using hs.1
  · change scales.2 + (arithmeticMapWithWork run scales.1).2 + 1 ≤ _
    have hsc : scales.2 ≤ queryScalesBitBudget B := hs.2
    unfold queryOnlineKeysBitBudget
    omega

end EditApproximation.BinaryFraction

end OAI
