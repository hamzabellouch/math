import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedSubsets
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.StreamPrimitiveWork
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTaskSpace

namespace OAI

/-! # Counted raw-leaf generation and sorting setup

Feasibility is checked before constructing any component family. Conversion
of an index list to a finite mask is charged quadratically in the ambient
index count; every generated list has length at most that count.
-/

namespace LowSpaceSubsetSum

namespace RepresentationLeaf

variable {n : ℕ}

/-- Scan the ambient indices in order. The quadratic charge includes
membership tests against a list representation of the finite domain. -/
def domainSort (V : Finset (Fin n)) : List (Fin n) × ℕ :=
  ((List.finRange n).filter (fun i => decide (i ∈ V)), 2 * (n + 1) ^ 2)

theorem domainSort_value (V : Finset (Fin n)) : (domainSort V).1 = V.sort (· ≤ ·) := by
  let l := (List.finRange n).filter (fun i => decide (i ∈ V))
  have hn : l.Nodup := (List.nodup_finRange n).filter _
  have hp : l.Pairwise (· ≤ ·) :=
    ((List.sortedLT_finRange n).pairwise.imp (fun h => le_of_lt h)).filter _
  have hf : l.toFinset = V := by ext; simp [l]
  have hs := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hp
  change l = V.sort (· ≤ ·)
  simpa only [hf] using hs.symm

@[simp] theorem domainSort_length (V : Finset (Fin n)) : (domainSort V).1.length = V.card := by
  rw [domainSort_value, Finset.length_sort]

theorem domainSort_work (V : Finset (Fin n)) : (domainSort V).2 ≤ 8 * (n + 1) ^ 2 := by
  change 2 * (n + 1) ^ 2 ≤ _
  omega

def countedEnumerate (L : RepresentationLeaf (Fin n)) : List (Occurrence (Fin n)) × ℕ :=
  if L.topCount ≤ L.top.card ∧ L.localCount ≤ L.mixer.card then
    let dt := domainSort L.top
    let dm := domainSort L.mixer
    let db := domainSort L.background
    let ts := CountedSubsets.select L.topCount dt.1
    let ms := CountedSubsets.select L.localCount dm.1
    let bs := CountedSubsets.all db.1
    let out := ((ts.1.map List.toFinset) ×ˢ (ms.1.map List.toFinset)) ×ˢ
      (bs.1.map List.toFinset)
    (out, dt.2 + dm.2 + db.2 + ts.2 + ms.2 + bs.2 +
      (n + 1) ^ 2 * (ts.1.length + ms.1.length + bs.1.length) +
      4 * out.length + 3 * (n + 1))
  else ([], 3 * (n + 1))

theorem countedEnumerate_value (L : RepresentationLeaf (Fin n)) :
    L.countedEnumerate.1 = L.enumerate := by
  unfold countedEnumerate
  split
  · simp only [domainSort_value, CountedSubsets.select_value, CountedSubsets.all_value]
    rfl
  · rename_i h
    symm
    apply List.eq_nil_of_length_eq_zero
    rw [enumerate_length, occurrences_card]
    rcases not_and_or.mp h with ht | hm
    · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ht), zero_mul, zero_mul]
    · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hm), mul_zero, zero_mul]

theorem countedEnumerate_work (L : RepresentationLeaf (Fin n)) :
    L.countedEnumerate.2 ≤ 64 * (n + 1) ^ 2 * (L.occurrences.card + 1) := by
  by_cases h : L.topCount ≤ L.top.card ∧ L.localCount ≤ L.mixer.card
  · have hct : L.top.card ≤ n := by simpa using Finset.card_le_univ L.top
    have hcm : L.mixer.card ≤ n := by simpa using Finset.card_le_univ L.mixer
    have hcb : L.background.card ≤ n := by simpa using Finset.card_le_univ L.background
    let a := L.top.card.choose L.topCount
    let b := L.mixer.card.choose L.localCount
    let c := 2 ^ L.background.card
    let N := L.occurrences.card
    have ha : 1 ≤ a := Nat.choose_pos h.1
    have hb : 1 ≤ b := Nat.choose_pos h.2
    have hc : 1 ≤ c := Nat.one_le_two_pow
    have hN : N = a * b * c := L.occurrences_card
    have hab : 1 ≤ a * b := by nlinarith
    have haN : a ≤ N := by
      rw [hN]
      calc
        a ≤ a * b := by simpa using Nat.mul_le_mul_left a hb
        _ ≤ a * b * c := by simpa using Nat.mul_le_mul_left (a * b) hc
    have hbN : b ≤ N := by
      rw [hN]
      calc
        b ≤ a * b := by simpa using Nat.mul_le_mul_right b ha
        _ ≤ a * b * c := by simpa using Nat.mul_le_mul_left (a * b) hc
    have hcN : c ≤ N := by rw [hN]; simpa using Nat.mul_le_mul_right c hab
    have ht := CountedSubsets.select_work L.topCount (domainSort L.top).1 (by simpa using h.1)
    have hm := CountedSubsets.select_work L.localCount (domainSort L.mixer).1 (by simpa using h.2)
    have hbwork := CountedSubsets.all_work (domainSort L.background).1
    simp only [domainSort_length] at ht hm hbwork
    have hta : (CountedSubsets.select L.topCount (domainSort L.top).1).2 ≤
        4 * (n + 1) ^ 2 * N := ht.trans (Nat.mul_le_mul
          (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by omega : L.top.card + 1 ≤ n + 1) 2)) haN)
    have hmb : (CountedSubsets.select L.localCount (domainSort L.mixer).1).2 ≤
        4 * (n + 1) ^ 2 * N := hm.trans (Nat.mul_le_mul
          (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by omega : L.mixer.card + 1 ≤ n + 1) 2)) hbN)
    have hbc : (CountedSubsets.all (domainSort L.background).1).2 ≤ 4 * N :=
      hbwork.trans (Nat.mul_le_mul_left 4 hcN)
    have hd0 := domainSort_work L.top
    have hd1 := domainSort_work L.mixer
    have hd2 := domainSort_work L.background
    have hsum : a + b + c ≤ 3 * N := by omega
    have hprod : (n + 1) ^ 2 * (a + b + c) ≤ 3 * (n + 1) ^ 2 * N := by
      nlinarith [Nat.mul_le_mul_left ((n + 1) ^ 2) hsum]
    have hp : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hpn : N ≤ (n + 1) ^ 2 * N := by nlinarith
    have hnp : n + 1 ≤ (n + 1) ^ 2 := by nlinarith only [Nat.zero_le n]
    simp only [Nat.mul_assoc] at hta hmb hprod
    unfold countedEnumerate
    simp only [h, List.length_product, List.length_map,
      CountedSubsets.select_length, CountedSubsets.all_length, domainSort_length]
    change _ + _ + _ + _ + _ + _ + (n + 1) ^ 2 * (a + b + c) +
      4 * (a * b * c) + 3 * (n + 1) ≤ 64 * (n + 1) ^ 2 * (N + 1)
    rw [← hN]
    calc
      _ ≤ 27 * (n + 1) ^ 2 + 11 * ((n + 1) ^ 2 * N) + 8 * N := by
        omega
      _ ≤ 27 * (n + 1) ^ 2 + 19 * ((n + 1) ^ 2 * N) := by omega
      _ ≤ _ := by nlinarith only [Nat.zero_le ((n + 1) ^ 2 * N), Nat.zero_le ((n + 1) ^ 2)]
  · simp only [countedEnumerate, h, ↓reduceIte]
    have hp : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
    nlinarith [Nat.zero_le ((n + 1) ^ 2 * L.occurrences.card)]

/-- The filter counter records predicate calls and output-array writes.
The cost of the predicate itself is handled separately. -/
def countedArray (L : RepresentationLeaf (Fin n)) (accept : Occurrence (Fin n) → Bool) :
    Array (Occurrence (Fin n)) × ℕ :=
  let e := L.countedEnumerate
  ((e.1.filter accept).toArray, e.2 + 2 * e.1.length)

theorem countedArray_value (L : RepresentationLeaf (Fin n))
    (accept : Occurrence (Fin n) → Bool) :
    (L.countedArray accept).1 = (L.enumerate.filter accept).toArray := by
  simp only [countedArray, countedEnumerate_value]

theorem countedArray_work (L : RepresentationLeaf (Fin n))
    (accept : Occurrence (Fin n) → Bool) :
    (L.countedArray accept).2 ≤ 68 * (n + 1) ^ 2 * (L.occurrences.card + 1) := by
  have he := L.countedEnumerate_work
  have hp : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hm : L.occurrences.card ≤ (n + 1) ^ 2 * (L.occurrences.card + 1) := by
    nlinarith [Nat.mul_le_mul_right (L.occurrences.card + 1) hp]
  simp only [countedArray, countedEnumerate_value, enumerate_length]
  nlinarith only [he, hm]

end RepresentationLeaf

namespace RepresentationPairData

variable {n : ℕ} (D : RepresentationPairData n)

/-- Counted generation, prefix filtering, and sorting of the two stored
leaf arrays. No row is materialized by this setup. -/
def countedArrays : (Array (Occ (n := n)) × Array (Occ (n := n))) × ℕ :=
  let l := D.left.countedArray D.acceptLeft
  let r := D.right.countedArray D.acceptRight
  let s := ResidueSort.counted r.1 D.wl D.lowModulus D.modulus
  ((l.1, s.1), l.2 + r.2 + s.2)

theorem countedArrays_value : D.countedArrays.1 = (D.leftArray, D.storedRight) := by
  simp only [countedArrays, RepresentationLeaf.countedArray_value,
    leftArray, rightArray, ResidueSort.counted_value, storedRight]

theorem countedArrays_work (hR : D.right.occurrences.card ≤ 2 ^ n) :
    D.countedArrays.2 ≤
      160 * (n + 1) ^ 2 * (D.left.occurrences.card + D.right.occurrences.card + 1) := by
  have hl := D.left.countedArray_work D.acceptLeft
  have hr := D.right.countedArray_work D.acceptRight
  have hs := D.counted_sort_work (D.rightArray_size_le.trans hR)
  have hp : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hn : 6 * n + 1 ≤ 7 * (n + 1) ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_right D.right.occurrences.card hn
  unfold countedArrays
  dsimp only
  rw [RepresentationLeaf.countedArray_value]
  change _ + _ + (ResidueSort.counted D.rightArray D.wl D.lowModulus D.modulus).2 ≤ _
  nlinarith only [hl, hr, hs, hm, hp]

end RepresentationPairData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem rawLeaf_capacity (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (j : Fin 2) (i : Fin 4) :
    (R.rawLeaf z g f (R.allocatedBackground z g hn hlog) j i).occurrences.card ≤
      compressionDictionaryCapacity n := by
  exact_mod_cast (R.rawLeaf_main_card z g f hn hlog hscale j i).trans
    (main_leaf_rate_le_capacity hn)

/-- Every residue, prefix, and sampler outcome uses the same setup bound.
The statement includes unsuccessful and overflowing tasks. -/
theorem schedule_pair_setup_work (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (q : ℕ) (hq : 0 < q) (z : ℕ) (side : Fin 2) (P : MaskRestriction n) (child : Fin 2) :
    let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
    D.countedArrays.2 ≤ inputScale R.input ^ 3 * (compressionDictionaryCapacity n + 1) := by
  dsimp only
  let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
  let C := compressionDictionaryCapacity n
  let u := inputScale R.input
  have hl : D.left.occurrences.card ≤ C :=
    R.rawLeaf_capacity h.1.1.1 h.1.1.2 h.1.2 hn hlog hscale side ⟨2 * child.val, by omega⟩
  have hr : D.right.occurrences.card ≤ C :=
    R.rawLeaf_capacity h.1.1.1 h.1.1.2 h.1.2 hn hlog hscale side ⟨2 * child.val + 1, by omega⟩
  have hC : C ≤ 2 ^ n := by
    unfold C compressionDictionaryCapacity
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hw := D.countedArrays_work (hr.trans hC)
  have hs : D.left.occurrences.card + D.right.occurrences.card + 1 ≤ 2 * (C + 1) := by omega
  have h1 := Nat.mul_le_mul_left (160 * (n + 1) ^ 2) hs
  have hnu : n + 1 ≤ u := by unfold u inputScale; omega
  have hu : 10000 ≤ u := by omega
  have h2 : 320 * (n + 1) ^ 2 ≤ u ^ 3 := by
    have hsq := Nat.pow_le_pow_left hnu 2
    have hm := Nat.mul_le_mul_right (u ^ 2) (show 320 ≤ u by omega)
    nlinarith only [hsq, hm]
  have h3 := Nat.mul_le_mul_right (C + 1) h2
  change D.countedArrays.2 ≤ u ^ 3 * (C + 1)
  nlinarith only [hw, h1, h3]

end RepresentationSetup
end LowSpaceSubsetSum

end OAI
