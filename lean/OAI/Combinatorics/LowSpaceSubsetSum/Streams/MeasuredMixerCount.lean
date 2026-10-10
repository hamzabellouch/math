import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredSumReader
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MixerParameterCount
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionWeights

namespace OAI

/-! # Mixer counts from generated and sorted half-sum arrays

All subset weights, comparisons, array copies and streamed sum keys are
charged. The returned natural number is the exact distinct-sum count.
-/

namespace LowSpaceSubsetSum.MeasuredMixerCount

variable {n : ℕ}

def sortedWeights (a : Fin n → ℤ) (indices : List (Fin n)) : Array ℤ × ℕ :=
  let raw := CompressionWeights.raw a indices
  let out := MeasuredSort.sort (fun x y : ℤ => (decide (x ≤ y), 1)) raw.1
  (out.1.toArray, raw.2 + out.2 + out.1.length + 1)

theorem sortedWeights_value (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (sortedWeights a (V.sort (· ≤ ·))).1 = MixerParameterCount.sortedWeights a V := by
  simp only [sortedWeights, CompressionWeights.raw_source, MeasuredSort.sort_value,
    MixerParameterCount.sortedWeights, CountedSort.sort_value]

theorem sortedWeights_size (a : Fin n → ℤ) (indices : List (Fin n)) :
    (sortedWeights a indices).1.size = 2 ^ indices.length := by
  simp only [sortedWeights, List.size_toArray, MeasuredSort.sort_value,
    List.length_mergeSort, CompressionWeights.raw_length]

theorem sortedWeights_sorted (a : Fin n → ℤ) (indices : List (Fin n)) :
    (sortedWeights a indices).1.toList.Pairwise (· ≤ ·) := by
  simp only [sortedWeights, List.toList_toArray, MeasuredSort.sort_value]
  simpa only [decide_eq_true_eq] using
    (List.pairwise_mergeSort (le := fun x y : ℤ => decide (x ≤ y))
      (fun x y z hxy hyz => decide_eq_true (le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz)))
      (fun x y => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total x y)
      (CompressionWeights.raw a indices).1)

def coefficient (n : ℕ) : ℕ := (n + 4) * n + 12 * n + 20

theorem sortedWeights_work (a : Fin n → ℤ) (indices : List (Fin n))
    (hi : indices.length ≤ n) :
    (sortedWeights a indices).2 ≤ coefficient n * 2 ^ indices.length := by
  have hr := CompressionWeights.raw_work a indices hi
  have hs := MeasuredSort.sort_work (fun x y : ℤ => (decide (x ≤ y), 1))
    1 (fun _ _ => le_rfl) (CompressionWeights.raw a indices).1 n
    (by rw [CompressionWeights.raw_length]; exact Nat.pow_le_pow_right (by decide) hi)
  have hp : 1 ≤ 2 ^ indices.length := Nat.one_le_two_pow
  simp only [CompressionWeights.raw_length] at hs
  change _ + _ + _ + 1 ≤ _
  simp only [MeasuredSort.sort_value, List.length_mergeSort, CompressionWeights.raw_length]
  unfold coefficient
  nlinarith only [hr, hs, hp]

def run (a : Fin n → ℤ) (left right : List (Fin n)) : ℕ × ℕ :=
  let xs := sortedWeights a left
  let ys := sortedWeights a right
  let out := MeasuredSumReader.count xs.1 ys.1 (sortedWeights_sorted a right)
  (out.1, xs.2 + ys.2 + out.2 + 3)

theorem run_source (a : Fin n → ℤ) (V W : Finset (Fin n)) (hd : Disjoint V W) :
    (run a (V.sort (· ≤ ·)) (W.sort (· ≤ ·))).1 = distinctSumCount a (V ∪ W) := by
  simp only [run, MeasuredSumReader.count_value, sortedWeights_value]
  exact MixerParameterCount.count_value a V W hd

theorem run_work (a : Fin n → ℤ) (left right : List (Fin n))
    (hleft : left.length ≤ n) (hright : right.length ≤ n) :
    (run a left right).2 ≤
      coefficient n * 2 ^ left.length + coefficient n * 2 ^ right.length +
      (4 * (left.length + 1) ^ 2 + 32) * 2 ^ left.length +
      (10 * left.length + 21) * 2 ^ (left.length + right.length) + 6 := by
  have hl := sortedWeights_work a left hleft
  have hr := sortedWeights_work a right hright
  have hc := MeasuredSumReader.count_work (sortedWeights a left).1
    (sortedWeights a right).1 (sortedWeights_sorted a right)
  simp only [sortedWeights_size, Nat.clog_pow 2 _ (by decide), ← pow_add] at hc
  change _ + _ + _ + 3 ≤ _
  omega

def mixerCount (a : Fin n → ℤ) (V : Finset (Fin n)) : ℕ × ℕ :=
  run a ((MixerParameterCount.firstHalf V).sort (· ≤ ·))
    ((MixerParameterCount.secondHalf V).sort (· ≤ ·))

theorem mixerCount_value (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (mixerCount a V).1 = distinctSumCount a V := by
  rw [mixerCount, run_source a _ _ (MixerParameterCount.halves_disjoint V),
    MixerParameterCount.halves_union]

end LowSpaceSubsetSum.MeasuredMixerCount

end OAI
