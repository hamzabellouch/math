import OAI.Combinatorics.EditApproximation.Numerics.OptimizerBits

namespace OAI

/-! Bit storage of the concrete materialized iterates.  The history bound
allows every previous iterate to remain live; it does not rely on a garbage
collector reclaiming old vector allocations. -/

namespace EditApproximation

open Finset

def rationalVectorStorageBits {d : ℕ} (values : Vector ℚ d) : ℕ :=
  ∑ i : Fin d, rationalEncodingBits (values.get i)

def optimizerStoredHistory {d : ℕ} (vertices : List (Vector ℚ d))
    (linear : Vector ℚ d) (G K : ℕ) : List (Vector ℚ d) :=
  (List.range (K + 1)).map fun j => (materializedOptimizerWithWork vertices linear G j).1

def rationalVectorListStorageBits {d : ℕ} (values : List (Vector ℚ d)) : ℕ :=
  (values.map rationalVectorStorageBits).sum

theorem rationalVectorStorageBits_le {d : ℕ} (values : Vector ℚ d) (B : ℕ)
    (hB : ∀ i, rationalEncodingBits (values.get i) ≤ B) :
    rationalVectorStorageBits values ≤ d * B := by
  calc
    _ ≤ ∑ _i : Fin d, B := Finset.sum_le_sum (fun i _ => hB i)
    _ = _ := by simp

theorem rationalVectorListStorageBits_le {d : ℕ} (values : List (Vector ℚ d)) (B : ℕ)
    (hB : ∀ value ∈ values, rationalVectorStorageBits value ≤ B) :
    rationalVectorListStorageBits values ≤ values.length * B := by
  unfold rationalVectorListStorageBits
  induction values with
  | nil => simp
  | cons value rest ih =>
    have hv := hB value List.mem_cons_self
    have hr := ih (fun v hv => hB v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem materializedOptimizerWithWork_uniform_encoding {d : ℕ}
    (vertices : List (Vector ℚ d)) (linear : Vector ℚ d) (G K B j : ℕ)
    (hvertices : vertices ≠ []) (hj : j ≤ K) (i : Fin d)
    (hinput : ∀ vertex ∈ vertices,
      (0 ≤ vertex.get i ∧ vertex.get i ≤ 1) ∧ Nat.size (vertex.get i).den ≤ B) :
    rationalEncodingBits ((materializedOptimizerWithWork vertices linear G j).1.get i) ≤
      2 * ((K + 1) * (2 * Nat.size (K + 1) + 2 + B) + 1) + 1 := by
  by_cases hjzero : j = 0
  · subst j
    cases vertices with
    | nil => exact False.elim (hvertices rfl)
    | cons vertex rest =>
      have hcoord := hinput vertex List.mem_cons_self
      have hnum := Nat.size_le_size (rational_numerator_bound (vertex.get i) 1 (by
        rw [abs_of_nonneg hcoord.1.1]
        exact hcoord.1.2))
      simp only [Nat.one_mul] at hnum
      change rationalEncodingBits (vertex.get i) ≤ _
      unfold rationalEncodingBits
      have hK : 1 ≤ K + 1 := by omega
      have hpositive : B ≤ 2 * Nat.size (K + 1) + 2 + B := by omega
      have hproduct := Nat.mul_le_mul hK hpositive
      omega
  · have hbound := materializedOptimizerWithWork_encoding vertices linear G j B
      hvertices (by omega) i hinput
    have hsize := Nat.size_le_size (by omega : j ≤ K + 1)
    have hproduct := Nat.mul_le_mul (by omega : j ≤ K + 1)
      (by omega : 2 * Nat.size j + 2 + B ≤ 2 * Nat.size (K + 1) + 2 + B)
    omega

theorem optimizerStoredHistory_storage_le {d : ℕ}
    (vertices : List (Vector ℚ d)) (linear : Vector ℚ d) (G K B : ℕ)
    (hvertices : vertices ≠ [])
    (hinput : ∀ vertex ∈ vertices, ∀ i,
      (0 ≤ vertex.get i ∧ vertex.get i ≤ 1) ∧ Nat.size (vertex.get i).den ≤ B) :
    rationalVectorListStorageBits (optimizerStoredHistory vertices linear G K) ≤
      (K + 1) * (d * (2 * ((K + 1) * (2 * Nat.size (K + 1) + 2 + B) + 1) + 1)) := by
  have hstorage := rationalVectorListStorageBits_le (optimizerStoredHistory vertices linear G K)
    (d * (2 * ((K + 1) * (2 * Nat.size (K + 1) + 2 + B) + 1) + 1)) (by
      intro value hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      apply rationalVectorStorageBits_le
      intro i
      exact materializedOptimizerWithWork_uniform_encoding vertices linear G K B j hvertices
        (by have := List.mem_range.mp hj; omega) i (fun vertex hv => hinput vertex hv i))
  simpa only [optimizerStoredHistory, List.length_map, List.length_range] using hstorage

end EditApproximation

end OAI
