import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MixerWeightCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SumReaderCells
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MixerHalfLists

namespace OAI

/-! # Complete half-array and streamed mixer-count storage

Both half arrays stay live throughout the tournament count. The input
domain is split once. No Cartesian list is constructed at any stage.
-/

namespace LowSpaceSubsetSum.MixerCountCells

variable {n : ℕ}

def run (a : Fin n → ℤ) (left right : List (Fin n)) : (ℕ × ℕ) × ℕ :=
  let xs := MixerWeightCells.sortedWeights a left
  let ys := MixerWeightCells.sortedWeights a right
  let hsorted : ys.1.1.toList.Pairwise (· ≤ ·) := by
    rw [MixerWeightCells.sortedWeights_value]
    exact MeasuredMixerCount.sortedWeights_sorted a right
  let out := SumReaderCells.count xs.1.1 ys.1.1 hsorted
  ((out.1.1, xs.1.2+ys.1.2+out.1.2+3),
    xs.2+ys.2+out.2+2*(xs.1.1.size+ys.1.1.size+1)+left.length+right.length+16)

theorem run_value (a : Fin n → ℤ) (left right : List (Fin n)) :
    (run a left right).1 = MeasuredMixerCount.run a left right := by
  simp only [run, MixerWeightCells.sortedWeights_value, SumReaderCells.count_value,
    MeasuredMixerCount.run]

theorem run_cells (a : Fin n → ℤ) (left right : List (Fin n))
    (hL : left.length ≤ n) (hR : right.length ≤ n) :
    (run a left right).2 ≤
      4096*(n+2)^2*(2^left.length+2^right.length+1) := by
  let xs := MixerWeightCells.sortedWeights a left
  let ys := MixerWeightCells.sortedWeights a right
  have hxs := MixerWeightCells.sortedWeights_cells a left hL
  have hys := MixerWeightCells.sortedWeights_cells a right hR
  have hl : xs.1.1.size = 2^left.length := by
    dsimp only [xs]
    rw [MixerWeightCells.sortedWeights_value, MeasuredMixerCount.sortedWeights_size]
  have hr : ys.1.1.size = 2^right.length := by
    dsimp only [ys]
    rw [MixerWeightCells.sortedWeights_value, MeasuredMixerCount.sortedWeights_size]
  have hsorted : ys.1.1.toList.Pairwise (· ≤ ·) := by
    dsimp only [ys]
    rw [MixerWeightCells.sortedWeights_value]
    exact MeasuredMixerCount.sortedWeights_sorted a right
  have hc := SumReaderCells.count_cells xs.1.1 ys.1.1 hsorted
  simp only [hl, hr, Nat.clog_pow 2 _ (by decide)] at hc
  have hdegree := Nat.pow_le_pow_left (show left.length+2 ≤ n+2 by omega) 2
  have hc' := hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1024 hdegree))
  have hp : n+2 ≤ (n+2)^2 := by nlinarith
  have ht₀ : 1 ≤ 2^left.length := Nat.one_le_two_pow
  have ht₁ : 1 ≤ 2^right.length := Nat.one_le_two_pow
  have hretained : 2*(2^left.length+2^right.length+1)+left.length+right.length+16 ≤
      32*(n+2)^2*(2^left.length+2^right.length+1) := by
    have h := Nat.mul_le_mul_right (2^left.length+2^right.length+1) hp
    nlinarith only [h, hL, hR, ht₀, ht₁]
  change xs.2+ys.2+(SumReaderCells.count xs.1.1 ys.1.1 hsorted).2+
    2*(xs.1.1.size+ys.1.1.size+1)+left.length+right.length+16 ≤ _
  rw [hl, hr]
  change xs.2 ≤ _ at hxs
  change ys.2 ≤ _ at hys
  nlinarith only [hxs, hys, hc', hretained, ht₀, ht₁]

def count (a : Fin n → ℤ) (xs : List (Fin n)) : (ℕ × ℕ) × ℕ :=
  let halves := MixerHalfLists.split xs
  let out := run a halves.1.1 halves.1.2
  ((out.1.1, halves.2+out.1.2+1), out.2+4*xs.length+16)

theorem count_value (a : Fin n → ℤ) (xs : List (Fin n)) :
    (count a xs).1 = MixerHalfLists.count a xs := by
  simp only [count, run_value, MixerHalfLists.count]

theorem count_cells (I : Instance n) (a : Fin n → ℤ) (xs : List (Fin n))
    (hn : 10000 ≤ n) (hx : xs.length ≤ n) :
    (count a xs).2 ≤ inputScale I^5*2^((xs.length+1)/2) := by
  have h := run_cells a (xs.take (xs.length/2)) (xs.drop (xs.length/2))
    (by simp only [List.length_take]; exact (Nat.min_le_right _ _).trans hx)
    (by simp only [List.length_drop]; omega)
  have hleft : (xs.take (xs.length/2)).length ≤ (xs.length+1)/2 := by
    simp only [List.length_take]
    omega
  have hright : (xs.drop (xs.length/2)).length ≤ (xs.length+1)/2 := by
    simp only [List.length_drop]
    omega
  have hp₀ := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hleft
  have hp₁ := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hright
  have hp : 1 ≤ 2^((xs.length+1)/2) := Nat.one_le_two_pow
  have hscaled := h.trans (Nat.mul_le_mul_left (4096*(n+2)^2)
    (show 2^(xs.take (xs.length/2)).length+2^(xs.drop (xs.length/2)).length+1 ≤
      3*2^((xs.length+1)/2) by omega))
  have hu : n+2 ≤ inputScale I := by unfold inputScale; omega
  have hcoeff : 16384*(n+2)^2 ≤ inputScale I^5 := by
    have hlow : 16384 ≤ inputScale I^3 := by
      calc
        _ ≤ 10000^3 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_left (by omega) 3
    have hsq := Nat.pow_le_pow_left hu 2
    exact (Nat.mul_le_mul hlow hsq).trans (by rw [← pow_add])
  have hfinal := Nat.mul_le_mul_right (2^((xs.length+1)/2)) hcoeff
  have hminor : 4*xs.length+16 ≤ 4096*(n+2)^2*2^((xs.length+1)/2) := by
    have hq : n+2 ≤ (n+2)^2 := by nlinarith
    have hm := Nat.mul_le_mul_left ((n+2)^2) hp
    simp only [Nat.mul_one] at hm
    have hbase : 4*xs.length+16 ≤ 4096*(n+2)^2 := by omega
    exact hbase.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 4096 hm)
  have hscaled' : (run a (xs.take (xs.length/2)) (xs.drop (xs.length/2))).2 ≤
      12288*((n+2)^2*2^((xs.length+1)/2)) := by
    calc
      _ ≤ 4096*(n+2)^2*(3*2^((xs.length+1)/2)) := hscaled
      _ = _ := by ring
  change (run a (xs.take (xs.length/2)) (xs.drop (xs.length/2))).2+4*xs.length+16 ≤ _
  simp only [Nat.mul_assoc] at hfinal hminor
  omega

end LowSpaceSubsetSum.MixerCountCells

end OAI
