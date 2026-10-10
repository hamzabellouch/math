import OAI.Combinatorics.EditApproximation.Queries.QueryChargedSeed

namespace OAI

namespace EditApproximation

section Seed
variable {M J n passes copies T S : ℕ}
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})
  (oracle : {child : ChargedPhysicalRequest M J n passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
  (readWork : {child : ChargedPhysicalRequest M J n passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → ℕ)

theorem queryChargedRead_work_bound (C : ℕ) (hc : ∀ key, readWork key ≤ C) (key) :
    (queryChargedRead parent key).work oracle readWork ≤ 7 * J + 33 + C := by
  have h := chargedPhysicalCodeWithWork_cost key.val
  have hr := hc key
  simp only [queryChargedRead, BitQuery.work]
  omega

private theorem seed_sum_bound {κ : Type*} (keys : List κ) (cost : κ → ℕ) (C : ℕ)
    (hc : ∀ key, cost key ≤ C) : (keys.map cost).sum ≤ keys.length * C := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have h := hc key
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def queryChargedSeedBitBudget (copies J B C : ℕ) : ℕ :=
  8 * B + 3 + (7 * J + 33 + C) + copies + 1 +
    copies * (7 * J + 33 + C + 3) + BinaryFraction.seedMedianBitBudget copies B + B + 1

theorem queryChargedSeedAt_bounds (N B C : ℕ) (multiplier : ℕ → ℕ) (q : TargetInterval n)
    (hB : 1 ≤ B) (hN : Nat.size N ≤ B) (hp : Nat.size parent.val.pass ≤ B)
    (hm : Nat.size (multiplier (parent.val.pass - 1)) + 2 ≤ B)
    (hv : ∀ key, (oracle key).width ≤ B) (hc : ∀ key, readWork key ≤ C) :
    ((queryChargedSeedAt parent N multiplier q).value oracle).width ≤ B ∧
      (queryChargedSeedAt parent N multiplier q).work oracle readWork ≤
        queryChargedSeedBitBudget copies J B C := by
  have heq := naturalEqualWithWork_cost parent.val.pass 0 B hp (by simp)
  have hr (key) := queryChargedRead_work_bound parent oracle readWork C hc key
  unfold queryChargedSeedAt
  split
  · constructor
    · exact hv _
    · simp only [BitQuery.work]
      have := hr ⟨.inl (parent.val.node, q), ChargedPhysicalRequest.coarse_rank_lt _ parent rfl⟩
      change (naturalEqualWithWork parent.val.pass 0).2 + 1 +
        (queryChargedRead parent _).work oracle readWork ≤ _
      unfold queryChargedSeedBitBudget
      omega
  · rename_i hpass
    let hpos := Nat.pos_of_ne_zero (fun h => hpass ((naturalEqualWithWork_value _ _).mpr h))
    let reader := queryChargedPreviousRead parent hpos q
    let words := (List.finRange copies).map fun copy => (reader copy).value oracle
    have hlen : words.length = copies := by simp only [words, List.length_map, List.length_finRange]
    have hwords : ∀ word ∈ words, word.width ≤ B := by
      intro word hw
      obtain ⟨copy, _, rfl⟩ := List.mem_map.mp hw
      exact hv _
    have hmedian := BinaryFraction.seedMedianWithWork_cost N (multiplier (parent.val.pass - 1)) words B hN hm hwords
    have hlength := BinaryFraction.seedMedianWithWork_length N (multiplier (parent.val.pass - 1)) words
    have hsum := seed_sum_bound (List.finRange copies) (fun copy => (reader copy).work oracle readWork + 3)
      (7 * J + 33 + C + 3) (fun copy => Nat.add_le_add_right (hr _) 3)
    simp only [List.length_finRange] at hsum
    rw [hlen] at hmedian
    constructor
    · simp only [BitQuery.value, BitQuery.value_collect, BitQuery.compute,
        BinaryFraction.querySeedMedianWithWork, BinaryFraction.ofNaturalWord_width]
      exact max_le (hlength.trans hN) hB
    · simp only [BitQuery.work, BitQuery.work_collect, BitQuery.compute, Nat.add_zero]
      change (naturalEqualWithWork parent.val.pass 0).2 + 1 +
        (copies + 1 + (((List.finRange copies).map fun copy => (reader copy).work oracle readWork + 3).sum +
          (BinaryFraction.querySeedMedianWithWork N (multiplier (parent.val.pass - 1)) words).2)) ≤ _
      unfold BinaryFraction.querySeedMedianWithWork queryChargedSeedBitBudget
      dsimp only
      omega

end Seed
end EditApproximation

end OAI
