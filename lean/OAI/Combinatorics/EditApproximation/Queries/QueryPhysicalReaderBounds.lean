import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalReaders

namespace OAI

namespace EditApproximation

private theorem reader_cost_sum {κ : Type*} (keys : List κ) (cost : κ → ℕ) (C : ℕ)
    (h : ∀ key ∈ keys, cost key ≤ C) : (keys.map cost).sum ≤ keys.length * C := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have hh := h key List.mem_cons_self
    have ht := ih (fun k hk => h k (List.mem_cons_of_mem key hk))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem queryMeanRead_bounds {ι : Type*} (count B C : ℕ)
    (reader : Fin count → BitQuery ι BinaryFraction)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hw : ∀ i, ((reader i).value oracle).width ≤ B)
    (hc : ∀ i, (reader i).work oracle readWork ≤ C) :
    ((queryMeanRead count reader).value oracle).width ≤ BinaryFraction.warmupAverageWordBudget count B ∧
      (queryMeanRead count reader).work oracle readWork ≤
        count + 1 + count * (C + 3) + BinaryFraction.warmupAverageBitBudget count B := by
  let inputs := List.ofFn fun i : Fin count => i
  let words := inputs.map fun i => (reader i).value oracle
  have hlen : words.length = count := by simp only [words, inputs, List.length_map, List.length_ofFn]
  have havg := BinaryFraction.warmupAverageWithWork_bounds words B (by
    intro w hw'
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw'
    exact hw i)
  rw [← BinaryFraction.queryMeanWithWork_eq_average count words hlen] at havg
  rw [hlen] at havg
  have hs := reader_cost_sum inputs (fun i => (reader i).work oracle readWork + 3) (C + 3)
    (fun i _ => Nat.add_le_add_right (hc i) 3)
  simp only [inputs, List.length_ofFn] at hs
  change (inputs.map fun i => (reader i).work oracle readWork + 3).sum ≤ count * (C + 3) at hs
  constructor
  · simpa only [queryMeanRead, BitQuery.value, BitQuery.value_collect, BitQuery.compute, words, inputs] using havg.1
  · rw [queryMeanRead_work]
    change count + 1 + (inputs.map fun i => (reader i).work oracle readWork + 3).sum +
      (BinaryFraction.queryMeanWithWork count words).2 ≤ _
    omega

section Physical
variable {M J n : ℕ} (copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
  (oracle : {child : PhysicalTableRequest M J n // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → BinaryFraction)
  (readWork : {child : PhysicalTableRequest M J n // child.combinedRank T S <
    (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} → ℕ)

theorem queryPhysicalWarmupRead_work_bound (W : ℕ) (hW : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork key ≤ W)
    (other : PhysicalNode M J) (hnode : node.1.val ≤ other.1.val) (j : ℕ) (hj : j ≤ T)
    (r : TargetInterval n) :
    (queryPhysicalWarmupRead copies pass copy T S t ht node q other hnode j hj r).work oracle readWork ≤
      7 * J + 30 + W := by
  exact (queryPhysicalTableRead_work copies T S _ _ oracle readWork).trans
    (Nat.add_le_add_left (hW _ rfl rfl) _)

theorem queryPhysicalCurrentRead_work_bound (W : ℕ) (hW : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork key ≤ W)
    (input : Fin M × TargetInterval n) :
    (queryPhysicalCurrentRead copies pass copy T S t node hbelow q input).work oracle readWork ≤
      7 * J + 30 + W := by
  exact (queryPhysicalTableRead_work copies T S _ _ oracle readWork).trans
    (Nat.add_le_add_left (hW _ rfl rfl) _)

theorem queryPhysicalEarlierRead_work_bound (B W : ℕ) (hW : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork key ≤ W)
    (htime : Nat.size t ≤ B) (input : Fin M × ℕ × TargetInterval n) (hi : Nat.size input.2.1 ≤ B) :
    (queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).work oracle readWork ≤
      8 * B + 7 * J + 32 + W := by
  have hcmp := binaryNaturalCompareWithWork_cost input.2.1 t
  have hr (child : {r : PhysicalTableRequest M J n // r.combinedRank T S <
      (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S})
      (hp : child.val.pass = pass) (hc : child.val.copy = copy) :
      (queryPhysicalTableRead copies T S _ child).work oracle readWork ≤ 7 * J + 30 + W :=
    (queryPhysicalTableRead_work copies T S _ child oracle readWork).trans
      (Nat.add_le_add_left (hW child hp hc) _)
  unfold queryPhysicalEarlierRead
  simp only [BitQuery.work]
  split
  · apply (Nat.add_le_add_left (hr _ rfl rfl) _).trans
    omega
  · simp only [BitQuery.work]
    omega

theorem queryPhysicalMassRead_bounds (B W : ℕ) (hW : ∀ key, key.val.pass = pass → key.val.copy = copy → readWork key ≤ W)
    (hw : ∀ key, (oracle key).width ≤ B) (input : Fin M × TargetInterval n) :
    ((queryPhysicalMassRead copies pass copy T S t ht node hbelow q input).value oracle).width ≤
        BinaryFraction.warmupAverageWordBudget T B ∧
      (queryPhysicalMassRead copies pass copy T S t ht node hbelow q input).work oracle readWork ≤
        T + 1 + T * (7 * J + 30 + W + 3) + BinaryFraction.warmupAverageBitBudget T B := by
  apply queryMeanRead_bounds T B (7 * J + 30 + W)
  · intro j
    exact hw _
  · intro j
    exact queryPhysicalWarmupRead_work_bound copies pass copy T S t ht node q oracle readWork W hW _ _ _ _ _

theorem queryPhysicalEarlierRead_width (B : ℕ) (hB : 2 ≤ B)
    (hw : ∀ key, (oracle key).width ≤ B) (input : Fin M × ℕ × TargetInterval n) :
    ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value oracle).width ≤ B := by
  unfold queryPhysicalEarlierRead
  simp only [BitQuery.value]
  split
  · exact hw _
  · exact (BinaryFraction.nat_width_le 0).trans (by simpa only [Nat.size_zero, Nat.zero_add] using hB)

theorem queryPhysicalEarlierRead_nonneg (hw : ∀ key, 0 ≤ (oracle key).value)
    (input : Fin M × ℕ × TargetInterval n) :
    0 ≤ ((queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).value oracle).value := by
  unfold queryPhysicalEarlierRead
  simp only [BitQuery.value]
  split
  · exact hw _
  · simp only [BitQuery.value, BinaryFraction.nat_value, Nat.cast_zero, le_refl]

end Physical
end EditApproximation

end OAI
