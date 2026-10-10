import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedSubsets
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedWeights
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedDedup
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredSort

namespace OAI

/-! # Executing raw and compact subset-weight generation

Indices are supplied in canonical input order. The raw generator constructs
the same sublists as the source program; every weight is evaluated by the
measured integer routine. Mapping uses an accumulator and one final reversal.
-/

namespace LowSpaceSubsetSum.CompressionWeights

variable {n : ℕ}

def weightsAcc (a : Fin n → ℤ) : List (List (Fin n)) → List ℤ → ℕ → List ℤ × ℕ
  | [], acc, work => (acc.reverse, work + acc.length + 1)
  | xs :: rest, acc, work =>
    let w := CountedWeights.weight a xs
    weightsAcc a rest (w.1 :: acc) (work + w.2 + 2)

theorem weightsAcc_value (a : Fin n → ℤ) (xs : List (List (Fin n)))
    (acc : List ℤ) (work : ℕ) :
    (weightsAcc a xs acc work).1 = acc.reverse ++ xs.map (fun x => weight a x.toFinset) := by
  induction xs generalizing acc work with
  | nil => simp only [weightsAcc, List.map_nil, List.append_nil]
  | cons x xs ih =>
    simp only [weightsAcc, ih, List.reverse_cons, CountedWeights.weight_value,
      List.map_cons, List.append_assoc, List.singleton_append]

theorem weightsAcc_work (a : Fin n → ℤ) (xs : List (List (Fin n)))
    (acc : List ℤ) (work K : ℕ) (hk : ∀ x ∈ xs, (CountedWeights.weight a x).2 ≤ K) :
    (weightsAcc a xs acc work).2 ≤ work + (K + 3) * xs.length + acc.length + 1 := by
  induction xs generalizing acc work with
  | nil => simp only [weightsAcc, List.length_nil, Nat.mul_zero, Nat.add_zero]; rfl
  | cons x xs ih =>
    have hx := hk x (by simp)
    have ht := ih ((CountedWeights.weight a x).1 :: acc)
      (work + (CountedWeights.weight a x).2 + 2) (fun y hy => hk y (by simp [hy]))
    simp only [List.length_cons] at ht
    simp only [weightsAcc, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

def raw (a : Fin n → ℤ) (indices : List (Fin n)) : List ℤ × ℕ :=
  let masks := CountedSubsets.all indices
  let out := weightsAcc a masks.1 [] 0
  (out.1, masks.2 + out.2 + 1)

theorem raw_value (a : Fin n → ℤ) (indices : List (Fin n)) :
    (raw a indices).1 = indices.sublists.map (fun x => weight a x.toFinset) := by
  simp only [raw, weightsAcc_value, List.reverse_nil, List.nil_append, CountedSubsets.all_value]

theorem raw_source (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (raw a (V.sort (· ≤ ·))).1 = rawWeightList a V := raw_value _ _

theorem raw_length (a : Fin n → ℤ) (indices : List (Fin n)) :
    (raw a indices).1.length = 2 ^ indices.length := by
  simp only [raw_value, List.length_map, List.length_sublists]

theorem raw_work (a : Fin n → ℤ) (indices : List (Fin n)) (hlen : indices.length ≤ n) :
    (raw a indices).2 ≤ ((n + 4) * n + 8) * 2 ^ indices.length + 2 := by
  have hw := weightsAcc_work a (CountedSubsets.all indices).1 [] 0 ((n + 4) * n + 1) (by
    intro xs hx
    have hsub : xs.Sublist indices := by
      rw [CountedSubsets.all_value] at hx
      exact List.mem_sublists.mp hx
    have hl : xs.length ≤ n := hsub.length_le.trans hlen
    exact (CountedWeights.weight_work a xs).trans (by gcongr))
  have he := CountedSubsets.all_work indices
  simp only [List.length_nil, Nat.zero_add, Nat.add_zero, CountedSubsets.all_length] at hw
  change _ + _ + 1 ≤ _
  nlinarith only [hw, he]

theorem raw_scale (I : Instance n) (hn : 10000 ≤ n) (a : Fin n → ℤ)
    (indices : List (Fin n)) (hlen : indices.length ≤ n) :
    (raw a indices).2 ≤ inputScale I ^ 3 * 2 ^ indices.length := by
  have hw := raw_work a indices hlen
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hu' : 10000 ≤ inputScale I := by omega
  have hp : ((n + 4) * n + 10) ≤ inputScale I ^ 3 := by
    have hs : (n + 4) * n ≤ 4 * inputScale I ^ 2 := by nlinarith only [hu, hn]
    have h1 : 1 ≤ inputScale I ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hm : 14 * inputScale I ^ 2 ≤ inputScale I ^ 3 := by
      calc
        _ ≤ inputScale I * inputScale I ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := (pow_succ' _ _).symm
    omega
  have hsize : 1 ≤ 2 ^ indices.length := Nat.one_le_two_pow
  have hm := Nat.mul_le_mul_right (2 ^ indices.length) hp
  nlinarith only [hw, hsize, hm]

def compact (a : Fin n → ℤ) (indices : List (Fin n)) : List ℤ × ℕ :=
  let initial := raw a indices
  let sorted := MeasuredSort.sort (fun x y : ℤ => (decide (x ≤ y), 1)) initial.1
  let out := CountedDedup.run sorted.1
  (out.1, initial.2 + sorted.2 + out.2 + 1)

theorem compact_source (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (compact a (V.sort (· ≤ ·))).1 = compactWeightList a V := by
  have h := CompactWeightWork.run_value a V
  simpa only [compact, raw_source, MeasuredSort.sort_value, CompactWeightWork.run,
    CountedSort.sort_value] using h

theorem compact_scale (I : Instance n) (hn : 10000 ≤ n) (a : Fin n → ℤ)
    (indices : List (Fin n)) (hlen : indices.length ≤ n) :
    (compact a indices).2 ≤ inputScale I ^ 4 * 2 ^ indices.length := by
  have hr := raw_scale I hn a indices hlen
  have hs := MeasuredSort.sort_work (fun x y : ℤ => (decide (x ≤ y), 1)) 1
    (fun _ _ => le_rfl) (raw a indices).1 n
    (by rw [raw_length]; exact Nat.pow_le_pow_right (by decide) hlen)
  have hd := CountedDedup.run_work
    (MeasuredSort.sort (fun x y : ℤ => (decide (x ≤ y), 1)) (raw a indices).1).1
  simp only [MeasuredSort.sort_value, List.length_mergeSort, raw_length] at hs hd
  have hu : n ≤ inputScale I := by unfold inputScale; omega
  have hu' : 10000 ≤ inputScale I := hn.trans hu
  have hu3 : inputScale I ≤ inputScale I ^ 3 := by
    simpa only [pow_one] using
      (pow_le_pow_right' (by omega : 1 ≤ inputScale I) (by decide : 1 ≤ 3))
  have h1 : 1 ≤ inputScale I ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hc : inputScale I ^ 3 + 12 * n + 7 ≤ inputScale I ^ 4 := by
    have hm : 20 * inputScale I ^ 3 ≤ inputScale I ^ 4 := by
      calc
        _ ≤ inputScale I * inputScale I ^ 3 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := (pow_succ' _ _).symm
    omega
  have hsize : 1 ≤ 2 ^ indices.length := Nat.one_le_two_pow
  have hm := Nat.mul_le_mul_right (2 ^ indices.length) hc
  change _ + _ + _ + 1 ≤ _
  simp only [MeasuredSort.sort_value]
  nlinarith only [hr, hs, hd, hsize, hm]

end LowSpaceSubsetSum.CompressionWeights

end OAI
