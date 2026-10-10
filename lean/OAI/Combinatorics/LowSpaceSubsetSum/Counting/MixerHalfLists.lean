import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredMixerCount

namespace OAI

/-! # Executed splitting of a stored mixer domain -/

namespace LowSpaceSubsetSum.MixerHalfLists

variable {n : ℕ}

def split (xs : List (Fin n)) : (List (Fin n) × List (Fin n)) × ℕ :=
  ((xs.take (xs.length / 2), xs.drop (xs.length / 2)), 4 * xs.length + 3)

theorem first_source (V : Finset (Fin n)) :
    (split (V.sort (· ≤ ·))).1.1 = (MixerParameterCount.firstHalf V).sort (· ≤ ·) := by
  simp only [split, Finset.length_sort, MixerParameterCount.firstHalf]
  symm
  exact (List.toFinset_sort (r := (· ≤ ·)) ((Finset.sort_nodup V (· ≤ ·)).take)).mpr
    ((Finset.pairwise_sort V (· ≤ ·)).sublist (List.take_sublist _ _))

theorem drop_set (V : Finset (Fin n)) :
    ((V.sort (· ≤ ·)).drop (V.card / 2)).toFinset = MixerParameterCount.secondHalf V := by
  let xs := V.sort (· ≤ ·)
  have hnd : (xs.take (V.card / 2) ++ xs.drop (V.card / 2)).Nodup := by
    rw [List.take_append_drop]
    exact Finset.sort_nodup V (· ≤ ·)
  have hd := (List.nodup_append.mp hnd).2.2
  ext i
  simp only [MixerParameterCount.secondHalf, Finset.mem_sdiff,
    MixerParameterCount.firstHalf, List.mem_toFinset]
  change i ∈ xs.drop (V.card / 2) ↔ i ∈ V ∧ i ∉ xs.take (V.card / 2)
  have hmem : i ∈ xs ↔ i ∈ V := Finset.mem_sort (· ≤ ·)
  have happ : i ∈ xs ↔ i ∈ xs.take (V.card / 2) ∨ i ∈ xs.drop (V.card / 2) := by
    rw [← List.mem_append, List.take_append_drop]
  constructor
  · intro hi
    exact ⟨hmem.mp (happ.mpr (Or.inr hi)), fun hj => hd i hj i hi rfl⟩
  · rintro ⟨hi, hn⟩
    exact (happ.mp (hmem.mpr hi)).resolve_left hn

theorem second_source (V : Finset (Fin n)) :
    (split (V.sort (· ≤ ·))).1.2 = (MixerParameterCount.secondHalf V).sort (· ≤ ·) := by
  simp only [split, Finset.length_sort]
  rw [← drop_set]
  symm
  exact (List.toFinset_sort (r := (· ≤ ·)) ((Finset.sort_nodup V (· ≤ ·)).drop)).mpr
    ((Finset.pairwise_sort V (· ≤ ·)).sublist (List.drop_sublist _ _))

def count (a : Fin n → ℤ) (xs : List (Fin n)) : ℕ × ℕ :=
  let halves := split xs
  let out := MeasuredMixerCount.run a halves.1.1 halves.1.2
  (out.1, halves.2 + out.2 + 1)

theorem count_source (a : Fin n → ℤ) (V : Finset (Fin n)) :
    (count a (V.sort (· ≤ ·))).1 = distinctSumCount a V := by
  simp only [count, first_source, second_source]
  exact MeasuredMixerCount.mixerCount_value a V

theorem count_work (a : Fin n → ℤ) (xs : List (Fin n)) (hx : xs.length ≤ n) :
    (count a xs).2 ≤
      MeasuredMixerCount.coefficient n * 2 ^ (xs.length / 2) +
      MeasuredMixerCount.coefficient n * 2 ^ (xs.length - xs.length / 2) +
      (4 * (xs.length / 2 + 1) ^ 2 + 32) * 2 ^ (xs.length / 2) +
      (10 * (xs.length / 2) + 21) * 2 ^ xs.length + 4 * xs.length + 10 := by
  have hl : (xs.take (xs.length / 2)).length = xs.length / 2 := by
    rw [List.length_take, Nat.min_eq_left (Nat.div_le_self _ _)]
  have hr : (xs.drop (xs.length / 2)).length = xs.length - xs.length / 2 :=
    List.length_drop
  have h := MeasuredMixerCount.run_work a (xs.take (xs.length / 2))
    (xs.drop (xs.length / 2)) (by rw [hl]; omega) (by rw [hr]; omega)
  rw [hl, hr, Nat.add_sub_of_le (Nat.div_le_self _ _)] at h
  change 4 * xs.length + 3 +
    (MeasuredMixerCount.run a (xs.take (xs.length / 2)) (xs.drop (xs.length / 2))).2 + 1 ≤ _
  omega


theorem count_scale (I : Instance n) (hn : 10000 ≤ n) (a : Fin n → ℤ)
    (xs : List (Fin n)) (hx : xs.length ≤ n) :
    (count a xs).2 ≤ inputScale I ^ 4 * 2 ^ xs.length := by
  let u := inputScale I
  have hu : n + 1 ≤ u := by dsimp [u, inputScale]; omega
  have hu0 : 10000 ≤ u := by omega
  have hnu : n ≤ u := by omega
  have hxu : xs.length / 2 + 1 ≤ u := by omega
  have hn2 := Nat.pow_le_pow_left hnu 2
  have hx2 := Nat.pow_le_pow_left hxu 2
  have hu2 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hc : MeasuredMixerCount.coefficient n ≤ 40 * u ^ 2 := by
    unfold MeasuredMixerCount.coefficient
    nlinarith only [hn2, hu, hu2]
  have hbig : 40 * u ^ 2 ≤ u ^ 3 := by
    calc
      _ ≤ u * u ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hp : 4 * (xs.length / 2 + 1) ^ 2 + 32 ≤ u ^ 3 := by omega
  have hlinear : 10 * (xs.length / 2) + 21 ≤ u ^ 3 := by
    nlinarith only [hxu, hu2, hbig]
  have hend : 4 * xs.length + 10 ≤ u ^ 3 := by
    nlinarith only [hx, hu, hu2, hbig]
  have hleft : 2 ^ (xs.length / 2) ≤ 2 ^ xs.length :=
    Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  have hright : 2 ^ (xs.length - xs.length / 2) ≤ 2 ^ xs.length :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hT : 1 ≤ 2 ^ xs.length := Nat.one_le_two_pow
  have hcL := Nat.mul_le_mul (hc.trans hbig) hleft
  have hcR := Nat.mul_le_mul (hc.trans hbig) hright
  have hpL := Nat.mul_le_mul hp hleft
  have hl := Nat.mul_le_mul_right (2 ^ xs.length) hlinear
  have he := hend.trans (Nat.le_mul_of_pos_right _ hT)
  have hw := count_work a xs hx
  have hf : 5 * u ^ 3 ≤ u ^ 4 := by
    calc
      _ ≤ u * u ^ 3 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hfinal := Nat.mul_le_mul_right (2 ^ xs.length) hf
  change (count a xs).2 ≤ u ^ 4 * 2 ^ xs.length
  nlinarith only [hw, hcL, hcR, hpL, hl, he, hfinal]

end LowSpaceSubsetSum.MixerHalfLists

end OAI
