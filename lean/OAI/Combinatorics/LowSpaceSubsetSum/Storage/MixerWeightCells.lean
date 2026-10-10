import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SubsetCells
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredMixerCount
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredSortCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationKeyCells

namespace OAI

/-! # Constructing the shared half-mixer weight arrays

Subset masks are index lists. Their weights are evaluated by actual
membership scans, then consumed by a tail accumulator. Sorting retains
only the bounded half-family, never the Cartesian stream of sums.
-/

namespace LowSpaceSubsetSum.MixerWeightCells

variable {n : ℕ}

def sumIndices (a : Fin n → ℤ) (mask : List (Fin n)) :
    List (Fin n) → (ℤ × ℕ) × ℕ
  | [] => ((0, 1), 4)
  | i :: xs =>
    let hit := RepresentationKeyCells.member i mask
    let rest := sumIndices a mask xs
    (((if hit.1.1 then a i else 0)+rest.1.1, hit.1.2+rest.1.2+3),
      max (hit.2+4) (rest.2+8))

theorem sumIndices_value (a : Fin n → ℤ) (mask xs : List (Fin n)) :
    (sumIndices a mask xs).1 = CountedWeights.sumIndices a mask xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [sumIndices, CountedWeights.sumIndices, RepresentationKeyCells.member_value, ih]

theorem sumIndices_cells (a : Fin n → ℤ) (mask xs : List (Fin n)) :
    (sumIndices a mask xs).2 ≤ 8*xs.length+2*mask.length+12 := by
  induction xs with
  | nil => simp only [sumIndices, List.length_nil]; omega
  | cons i xs ih =>
    have h := RepresentationKeyCells.member_cells i mask
    simp only [sumIndices, List.length_cons]
    omega

def weight (a : Fin n → ℤ) (mask : List (Fin n)) : (ℤ × ℕ) × ℕ :=
  let r := sumIndices a mask (List.ofFn id)
  (r.1, r.2+2*n+4)

theorem weight_value (a : Fin n → ℤ) (mask : List (Fin n)) :
    (weight a mask).1 = CountedWeights.weight a mask := sumIndices_value _ _ _

theorem weight_cells (a : Fin n → ℤ) (mask : List (Fin n)) (hm : mask.length ≤ n) :
    (weight a mask).2 ≤ 12*n+16 := by
  have h := sumIndices_cells a mask (List.ofFn id)
  simp only [List.length_ofFn] at h
  change _+2*n+4 ≤ _
  omega

def weightsAcc (a : Fin n → ℤ) :
    List (List (Fin n)) → List ℤ → ℕ → ℕ → (List ℤ × ℕ) × ℕ
  | [], acc, work, peak => ((acc.reverse, work+acc.length+1), max peak (2*acc.length+4))
  | mask :: rest, acc, work, peak =>
    let w := weight a mask
    weightsAcc a rest (w.1.1::acc) (work+w.1.2+2)
      (max peak (2*(rest.length+acc.length+1)+w.2+16))

theorem weightsAcc_value (a : Fin n → ℤ) (xs : List (List (Fin n)))
    (acc : List ℤ) (work peak : ℕ) :
    (weightsAcc a xs acc work peak).1 = CompressionWeights.weightsAcc a xs acc work := by
  induction xs generalizing acc work peak with
  | nil => rfl
  | cons x xs ih => simp only [weightsAcc, CompressionWeights.weightsAcc, weight_value, ih]

theorem weightsAcc_cells (a : Fin n → ℤ) (xs : List (List (Fin n)))
    (acc : List ℤ) (work peak : ℕ) (hm : ∀ x ∈ xs, x.length ≤ n) :
    (weightsAcc a xs acc work peak).2 ≤
      max peak (2*(xs.length+acc.length)+12*n+32) := by
  induction xs generalizing acc work peak with
  | nil => simp only [weightsAcc, List.length_nil, Nat.zero_add]; omega
  | cons x xs ih =>
    have hx := weight_cells a x (hm x (by simp))
    have h := ih ((weight a x).1.1::acc) (work+(weight a x).1.2+2)
      (max peak (2*(xs.length+acc.length+1)+(weight a x).2+16))
      (fun y hy => hm y (by simp [hy]))
    simp only [weightsAcc, List.length_cons] at h ⊢
    omega

def raw (a : Fin n → ℤ) (indices : List (Fin n)) : (List ℤ × ℕ) × ℕ :=
  let masks := SubsetCells.all 1 indices
  let out := weightsAcc a masks.1.1 [] 0 0
  ((out.1.1, masks.1.2+out.1.2+1),
    masks.2+out.2+(n+2)*(masks.1.1.length+1)+16)

theorem raw_value (a : Fin n → ℤ) (indices : List (Fin n)) :
    (raw a indices).1 = CompressionWeights.raw a indices := by
  simp only [raw, weightsAcc_value, SubsetCells.all_value, CompressionWeights.raw]

theorem raw_cells (a : Fin n → ℤ) (indices : List (Fin n)) (hi : indices.length ≤ n) :
    (raw a indices).2 ≤ 64*(n+2)*(2^indices.length+1) := by
  have hg := SubsetCells.all_cells 1 indices
  have hl : (SubsetCells.all 1 indices).1.1.length = 2^indices.length := by
    rw [SubsetCells.all_value, CountedSubsets.all_length]
  have hw := weightsAcc_cells a (SubsetCells.all 1 indices).1.1 [] 0 0 (by
    intro mask hm
    rw [SubsetCells.all_value, CountedSubsets.all_value] at hm
    exact (List.mem_sublists.mp hm).length_le.trans hi)
  simp only [List.length_nil, Nat.add_zero, Nat.zero_max, hl] at hw
  have hg' := hg.trans (Nat.mul_le_mul_right (2^indices.length)
    (Nat.mul_le_mul_left 16 (show indices.length+1 ≤ n+2 by omega)))
  have hT : 1 ≤ 2^indices.length := Nat.one_le_two_pow
  change (SubsetCells.all 1 indices).2+_+_+16 ≤ _
  rw [hl]
  nlinarith only [hg', hw, hT]

def compare (x y : ℤ) : (Bool × ℕ) × ℕ := ((decide (x ≤ y), 1), 4)

def sortedWeights (a : Fin n → ℤ) (indices : List (Fin n)) : (Array ℤ × ℕ) × ℕ :=
  let r := raw a indices
  let s := MeasuredSortCells.run 1 compare (Nat.clog 2 r.1.1.length) r.1.1
  ((s.1.1.toArray, r.1.2+s.1.2+s.1.1.length+1), r.2+s.2+4*(r.1.1.length+1)+16)

theorem sortedWeights_value (a : Fin n → ℤ) (indices : List (Fin n)) :
    (sortedWeights a indices).1 = MeasuredMixerCount.sortedWeights a indices := by
  simp only [sortedWeights, raw_value, MeasuredSortCells.run_value,
    MeasuredMixerCount.sortedWeights, MeasuredSort.sort, compare]

theorem sortedWeights_cells (a : Fin n → ℤ) (indices : List (Fin n)) (hi : indices.length ≤ n) :
    (sortedWeights a indices).2 ≤ 256*(n+2)^2*(2^indices.length+1) := by
  have hr := raw_cells a indices hi
  have hl : (raw a indices).1.1.length = 2^indices.length := by
    rw [raw_value, CompressionWeights.raw_length]
  have hs := MeasuredSortCells.run_cells 1 compare 4 (fun _ _ => le_rfl)
    (Nat.clog 2 (raw a indices).1.1.length) (raw a indices).1.1
  simp only [hl, Nat.clog_pow 2 _ (by decide)] at hs
  have hN : indices.length+1 ≤ n+2 := by omega
  have hT : 1 ≤ 2^indices.length := Nat.one_le_two_pow
  have hsort := hs.trans (Nat.mul_le_mul hN
    (show 24*(1+2)*(2^indices.length+1)+4 ≤ 76*(2^indices.length+1) by omega))
  have hminor : 4*(2^indices.length+1)+16 ≤ 12*(n+2)*(2^indices.length+1) := by
    nlinarith only [hT]
  have hdegree : n+2 ≤ (n+2)^2 := by nlinarith
  have hfinal := Nat.mul_le_mul_right (2^indices.length+1) hdegree
  change (raw a indices).2+_+4*((raw a indices).1.1.length+1)+16 ≤ _
  rw [hl]
  simp only [Nat.clog_pow 2 _ (by decide)]
  simp only [Nat.mul_assoc] at hr hsort hminor hfinal ⊢
  nlinarith only [hr, hsort, hminor, hfinal]

end LowSpaceSubsetSum.MixerWeightCells

end OAI
