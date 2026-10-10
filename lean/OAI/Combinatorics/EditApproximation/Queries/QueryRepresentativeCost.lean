import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSupportCost
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeReads

namespace OAI

namespace EditApproximation.BinaryFraction

def queryEarlierRepresentativesLength (P F exponent B : ℕ) : ℕ :=
  (B + 1) * ((64 * F * P + 2) ^ 2 +
    ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1)

def queryEarlierRepresentativesBitBudget (P F exponent B R : ℕ) : ℕ :=
  let groups := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let L := (P + 1) ^ 2
  R + localRepresentativesBitBudget P F B * (R + 2) + queryGroupKeysBitBudget F exponent B +
    groups * (cellCentersBitBudget P P (16 * B + 200) * (R + 1) + 5 * L + 4) +
    queryOnlineKeysBitBudget B + 2 * ((B + 1) * (64 * F * P + 2) ^ 2) + groups * L + 4

theorem queryEarlierRepresentativesWithWork_bounds {n : ℕ} (N P F exponent B R : ℕ)
    (hP : 0 < P) (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ)
    (q : TargetInterval n) (hB : 8 ≤ B) (hN : Nat.size N ≤ B)
    (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F) (hPb : Nat.size P ≤ B)
    (hn : Nat.size n ≤ B) (he : exponent + 1 ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hR : ∀ r, (initial r).2 ≤ R)
    (hw : 0 ≤ (initial q).1.value) (hPd : ∃ e : ℕ, P = 2 ^ e) :
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1.length ≤
      queryEarlierRepresentativesLength P F exponent B ∧
    (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).2 ≤
      queryEarlierRepresentativesBitBudget P F exponent B R := by
  let reps := localRepresentativeReadWithWork N P F a initial q
  let groups := queryGroupKeysWithWork N F exponent a (initial q).1 q
  let centers := fun key : ℕ × (ℕ × ℕ) =>
    cellCentersReadWithWork P F key.1 a (inversePowerTwo exponent) initial key.2
  let run := fun key : ℕ × (ℕ × ℕ) =>
    let labeled := arithmeticMapWithWork (fun r => ((key.1, r), 1)) (centers key).1
    (labeled.1, (centers key).2 + labeled.2 + 1)
  let cells := arithmeticFlatMapWithWork run groups.1
  let online := queryOnlineKeysWithWork N P F hP a (initial q).1 q
  let L := (P + 1) ^ 2
  let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let C := cellCentersBitBudget P P (16 * B + 200) * (R + 1)
  have hs := queryScalesWithWork_bounds N F B a (initial q).1 (by omega) hN hF ha (hi q)
  have hwlen : (dyadicQueryWindow N (initial q).1.value a.value F).length ≤ B + 1 := by
    simpa only [queryScalesWithWork_value] using hs.1
  have hrlen : reps.1.length ≤ (B + 1) * (64 * F * P + 2) ^ 2 := by
    rw [(localRepresentativeReadWithWork_eq_cost N P F a initial q R hR).1,
      localRepresentativesWithWork_value N P F hP a (fun r => (initial r).1) q]
    exact (localRefinementRepresentatives_length N P F a.value (fun r => (initial r).1.value) q hP hFpos).trans
      (Nat.mul_le_mul_right _ hwlen)
  have hrc := localRepresentativeReadWithWork_cost N P F B R a initial q
    (by omega) hN hF hFpos hPb hP hn ha hi hR
  have hg := queryGroupKeysWithWork_bounds N F exponent B a (initial q).1 q
    (by omega) hN hF hFpos he hn ha (hi q) hw
  have ho := queryOnlineKeysWithWork_bounds N P F B hP a (initial q).1 q
    (by omega) hN hF hFpos hPb hn ha (hi q)
  have ht : 0 ≤ (inversePowerTwo exponent).value ∧ (inversePowerTwo exponent).value ≤ 1 := by
    rw [inversePowerTwo_value]
    exact ⟨by positivity, zpow_le_one_of_nonpos₀ (by norm_num) (by omega)⟩
  have hc (key : ℕ × (ℕ × ℕ)) (hk : key ∈ groups.1) :
      (centers key).1.length ≤ L ∧ (centers key).2 ≤ C := by
    obtain ⟨hb, hd, hleft, hright⟩ := hg.2.2 key hk
    have hv := cellCentersReadWithWork_eq_cost P F key.1 a (inversePowerTwo exponent) initial key.2 R hR
    constructor
    · rw [hv.1, cellCentersWithWork_value P F key.1 a (inversePowerTwo exponent)
        (fun r => (initial r).1) key.2 hP]
      exact cellRepresentativeStates_length_le a.value (fun r => (initial r).1.value)
        (inversePowerTwo exponent).value key.2 ht hd hPd
    · apply hv.2.trans
      apply Nat.mul_le_mul_right
      apply cellCentersWithWork_uniform_cost P F key.1 (16 * B + 200) a (inversePowerTwo exponent)
        (fun r => (initial r).1) key.2 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by rw [inversePowerTwo_width]; omega)
        (fun r => (hi r).trans (by omega)) (by omega) (by omega) ht hd hPd
  have hrun (key : ℕ × (ℕ × ℕ)) (hk : key ∈ groups.1) :
      (run key).1.length ≤ L ∧ (run key).2 ≤ C + 4 * L + 1 := by
    have hh := hc key hk
    have hm := (arithmeticMapWithWork_cost (fun r => ((key.1, r), 1)) (centers key).1 1
      (fun _ _ => le_rfl)).trans (Nat.mul_le_mul_right _ hh.1)
    constructor
    · simpa only [run, arithmeticMapWithWork_value, List.length_map] using hh.1
    · change (centers key).2 + _ + 1 ≤ _
      simp only [Nat.reduceAdd] at hm
      rw [Nat.mul_comm L 4] at hm
      omega
  have hcl := (arithmeticFlatMapWithWork_length run groups.1 L
    (fun key hk => (hrun key hk).1)).trans (Nat.mul_le_mul_right _ hg.1)
  have hcc := (arithmeticFlatMapWithWork_cost run groups.1 (C + 4 * L + 1) L
    (fun key hk => (hrun key hk).2) (fun key hk => (hrun key hk).1)).trans
      (Nat.mul_le_mul_right _ hg.1)
  change cells.2 ≤ G * (C + 4 * L + 1 + L + 3) at hcc
  rw [show C + 4 * L + 1 + L + 3 = C + 5 * L + 4 by omega] at hcc
  have hgw : groups.2 ≤ queryGroupKeysBitBudget F exponent B := hg.2.1
  have how : online.2 ≤ queryOnlineKeysBitBudget B := ho.2
  have hrepw : reps.2 ≤ localRepresentativesBitBudget P F B * (R + 2) := hrc
  constructor
  · rw [queryEarlierRepresentativesWithWork_value N P F exponent hP a initial q R hR]
    exact (queryEarlierRepresentatives_length N P F exponent a.value (fun r => (initial r).1.value)
      q hPd hFpos hw).trans (Nat.mul_le_mul_right _ hwlen)
  · change (initial q).2 + reps.2 + groups.2 + cells.2 + online.2 +
      2 * reps.1.length + cells.1.length + 4 ≤ _
    change _ ≤ R + localRepresentativesBitBudget P F B * (R + 2) + queryGroupKeysBitBudget F exponent B +
      G * (C + 5 * L + 4) + queryOnlineKeysBitBudget B +
      2 * ((B + 1) * (64 * F * P + 2) ^ 2) + G * L + 4
    have hr2 := Nat.mul_le_mul_left 2 hrlen
    have hq := hR q
    change cells.1.length ≤ G * L at hcl
    omega

end EditApproximation.BinaryFraction

end OAI
