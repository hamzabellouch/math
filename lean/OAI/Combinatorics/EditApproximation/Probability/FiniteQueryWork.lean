import OAI.Combinatorics.EditApproximation.Refinement.PhysicalWarmupQuery
import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoWork

namespace OAI

/-! Exact read costs for the finite query combinators used in warmup
and refinement. In particular, a collected value is computed once and
is reused by the continuation's local arithmetic. -/

namespace EditApproximation.FiniteQuery

theorem keys_bind {ι : Type*} (oracle : ι → ℚ)
    (program : FiniteQuery ι) (next : ℚ → FiniteQuery ι) :
    (bind program next).keys oracle = program.keys oracle ++
      (next (program.value oracle)).keys oracle := by
  induction program with
  | done result => rfl
  | read key continuation ih =>
    simpa only [bind, keys, value, List.cons_append] using
      congrArg (List.cons key) (ih (oracle key))

theorem keys_collect {ι κ : Type*} (oracle : ι → ℚ)
    (reader : κ → FiniteQuery ι) (inputs : List κ) (next : List ℚ → FiniteQuery ι) :
    (collect reader inputs next).keys oracle =
      inputs.flatMap (fun input => (reader input).keys oracle) ++
      (next (inputs.map fun input => (reader input).value oracle)).keys oracle := by
  induction inputs generalizing next with
  | nil => rfl
  | cons input inputs ih =>
    simp only [collect, keys_bind, ih, List.flatMap_cons, List.map_cons, List.append_assoc]

theorem keys_all_collect {ι κ : Type*} (oracle : ι → ℚ) (predicate : ι → Prop)
    (reader : κ → FiniteQuery ι) (inputs : List κ) (next : List ℚ → FiniteQuery ι)
    (hreader : ∀ input ∈ inputs, ∀ key ∈ (reader input).keys oracle, predicate key)
    (hnext : ∀ values key, key ∈ (next values).keys oracle → predicate key) :
    ∀ key ∈ (collect reader inputs next).keys oracle, predicate key := by
  rw [keys_collect]
  intro key hkey
  rcases List.mem_append.mp hkey with hreaderKey | hnextKey
  · obtain ⟨input, hi, hk⟩ := List.mem_flatMap.mp hreaderKey
    exact hreader input hi key hk
  · exact hnext _ key hnextKey

theorem cost_bind {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) (next : ℚ → FiniteQuery ι) :
    (bind program next).cost oracle weight = program.cost oracle weight +
      (next (program.value oracle)).cost oracle weight := by
  induction program with
  | done result => simp only [bind, cost, value, Nat.zero_add]
  | read key continuation ih =>
    simp only [bind, cost, value, ih, Nat.add_assoc]

theorem cost_collect {ι κ : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (reader : κ → FiniteQuery ι) (keys : List κ) (next : List ℚ → FiniteQuery ι) :
    (collect reader keys next).cost oracle weight =
      (keys.map fun key => (reader key).cost oracle weight).sum +
      (next (keys.map fun key => (reader key).value oracle)).cost oracle weight := by
  induction keys generalizing next with
  | nil => simp only [collect, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons key keys ih =>
    simp only [collect, cost_bind, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem keys_length_eq_cost_one {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι) :
    (program.keys oracle).length = program.cost oracle (fun _ => 1) := by
  rw [cost_eq_sum]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_one]

theorem collect_cost_le {ι κ : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (reader : κ → FiniteQuery ι) (keys : List κ) (next : List ℚ → FiniteQuery ι)
    (readerBound continuationBound : ℕ)
    (hreader : ∀ key ∈ keys, (reader key).cost oracle weight ≤ readerBound)
    (hnext : (next (keys.map fun key => (reader key).value oracle)).cost oracle weight ≤
      continuationBound) :
    (collect reader keys next).cost oracle weight ≤ keys.length * readerBound + continuationBound := by
  rw [cost_collect]
  apply Nat.add_le_add _ hnext
  calc
    (keys.map fun key => (reader key).cost oracle weight).sum ≤
        (keys.map fun _ => readerBound).sum := List.sum_le_sum (by simpa using hreader)
    _ = keys.length * readerBound := by simp

end EditApproximation.FiniteQuery

end OAI
