import OAI.Combinatorics.EditApproximation.Queries.QueryCellStateCost
import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineKeyCost

namespace OAI

/-! The complete initial-support gather, including repeated cells and
unfiltered raw centers, has a local-parameter bound. -/

namespace EditApproximation.BinaryFraction

def queryInitialSupportLength (P F exponent B : ℕ) : ℕ :=
  let raw := (B + 1) * (64 * F * P + 2) ^ 2
  let groups := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  1 + raw + groups * P ^ 2 + (B + 1)

def queryInitialSupportBitBudget (P F exponent B : ℕ) : ℕ :=
  let raw := (B + 1) * (64 * F * P + 2) ^ 2
  let groups := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  queryRawCentersBitBudget P F B + queryGroupKeysBitBudget F exponent B +
    groups * (queryCellStatesBitBudget P exponent B + P ^ 2 + 3) +
    queryOnlineKeysBitBudget B + 4 * (B + 1) + 2 * raw + groups * P ^ 2 + 5

theorem queryInitialSupportWithWork_bounds {n : ℕ} (N P F exponent B : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hFpos : 1 ≤ F) (hPb : Nat.size P ≤ B) (hn : Nat.size n ≤ B)
    (he : exponent + 1 ≤ B) (ha : a.width ≤ B) (hv : value.width ≤ B)
    (hw : 0 ≤ value.value) (hPd : ∃ e : ℕ, P = 2 ^ e) :
    (queryInitialSupportWithWork N P F exponent hP a value q).1.length ≤
      queryInitialSupportLength P F exponent B ∧
    (queryInitialSupportWithWork N P F exponent hP a value q).2 ≤
      queryInitialSupportBitBudget P F exponent B := by
  let raw := queryRawCentersWithWork N P F a value q
  let groups := queryGroupKeysWithWork N F exponent a value q
  let run := fun key : ℕ × (ℕ × ℕ) => queryCellStatesWithWork n P key.1 exponent key.2
  let cells := arithmeticFlatMapWithWork run groups.1
  let online := queryOnlineKeysWithWork N P F hP a value q
  let onlineStates := arithmeticMapWithWork (fun key : ℕ × TargetInterval n => (key.2, 1)) online.1
  let R := (B + 1) * (64 * F * P + 2) ^ 2
  let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  have hr := queryRawCentersWithWork_bounds N P F B a value q hB hN hF hFpos hP hPb hn ha hv
  have hg := queryGroupKeysWithWork_bounds N F exponent B a value q (by omega) hN hF hFpos he hn ha hv hw
  have ho := queryOnlineKeysWithWork_bounds N P F B hP a value q (by omega) hN hF hFpos hPb hn ha hv
  have hrun (key : ℕ × (ℕ × ℕ)) (hk : key ∈ groups.1) :
      (run key).1.length ≤ P ^ 2 ∧ (run key).2 ≤ queryCellStatesBitBudget P exponent B := by
    obtain ⟨hb, hd, hc⟩ := hg.2.2 key hk
    exact queryCellStatesWithWork_bounds n P key.1 exponent B key.2 hP hPb hb he hn hc hd hPd
  have hcl : cells.1.length ≤ G * P ^ 2 :=
    (arithmeticFlatMapWithWork_length run groups.1 (P ^ 2) (fun key hk => (hrun key hk).1)).trans
      (Nat.mul_le_mul_right _ hg.1)
  have hcw := (arithmeticFlatMapWithWork_cost run groups.1
    (queryCellStatesBitBudget P exponent B) (P ^ 2)
    (fun key hk => (hrun key hk).2) (fun key hk => (hrun key hk).1)).trans
      (Nat.mul_le_mul_right _ hg.1)
  change cells.2 ≤ G * (queryCellStatesBitBudget P exponent B + P ^ 2 + 3) at hcw
  have hom := (arithmeticMapWithWork_cost (fun key : ℕ × TargetInterval n => (key.2, 1))
    online.1 1 (fun _ _ => le_rfl)).trans (Nat.mul_le_mul_right _ ho.1)
  change onlineStates.2 ≤ (B + 1) * (1 + 3) at hom
  have hol : onlineStates.1.length ≤ B + 1 := by
    simpa only [onlineStates, arithmeticMapWithWork_value, List.length_map] using ho.1
  have hrl : raw.1.length ≤ R := hr.1
  have hrw : raw.2 ≤ queryRawCentersBitBudget P F B := hr.2
  have hgw : groups.2 ≤ queryGroupKeysBitBudget F exponent B := hg.2.1
  have how : online.2 ≤ queryOnlineKeysBitBudget B := ho.2
  constructor
  · change (q :: (raw.1 ++ cells.1 ++ onlineStates.1)).length ≤ _
    simp only [List.length_cons, List.length_append]
    change _ ≤ 1 + R + G * P ^ 2 + (B + 1)
    omega
  · change raw.2 + groups.2 + cells.2 + online.2 + onlineStates.2 +
      2 * raw.1.length + cells.1.length + 5 ≤ _
    have hr2 := Nat.mul_le_mul_left 2 hrl
    change _ ≤ queryRawCentersBitBudget P F B + queryGroupKeysBitBudget F exponent B +
      G * (queryCellStatesBitBudget P exponent B + P ^ 2 + 3) +
      queryOnlineKeysBitBudget B + 4 * (B + 1) + 2 * R + G * P ^ 2 + 5
    rw [Nat.mul_comm (B + 1) (1 + 3)] at hom
    norm_num only at hom
    omega

end EditApproximation.BinaryFraction

end OAI
