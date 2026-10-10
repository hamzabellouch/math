import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionArrayBuild

namespace OAI

/-! # Work of constructing the compression trial's shared arrays -/

namespace LowSpaceSubsetSum.CompressionArrayBuild

open scoped BigOperators
variable {n : ℕ}

theorem source_lengths (D : CompressionData n) (e : Equiv.Perm (Fin n)) (hn : 10000 ≤ n) :
    (∀ i, ((source D e).compact i).length ≤ (n + 1) / 2) ∧
    (source D e).left.length ≤ (n + 1) / 2 ∧
    (∀ i, ((source D e).right i).length ≤ (n + 1) / 2) := by
  have hc (i : Fin 7) : ((source D e).compact i).length = compressionHalfSize n := by
    simp only [source, Finset.length_sort, CompressionData.block, permuteSubset,
      Finset.card_map, compressionBlock_card]
  simp only [source, Finset.length_sort, D.leftRaw_card, D.rightRaw_card]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [show (D.block e i).card = compressionHalfSize n from by
      simpa only [source, Finset.length_sort] using hc i, compressionHalfSize_eq]
    omega
  · unfold compressionLeftRawSize compressionRightRawSize
    rw [compressionHalfSize_eq]
    omega
  · intro i
    unfold compressionRawHalfSize compressionRightRawSize
    split <;> omega

theorem compact_work_source (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (hn : 10000 ≤ n) :
    (∑ i : Fin 7, (compactLists D.weights (source D e))[i.val].2) ≤
      7 * inputScale D.input ^ 4 * 2 ^ ((n + 1) / 2) := by
  have hl := (source_lengths D e hn).1
  have hb (i : Fin 7) : (compactLists D.weights (source D e))[i.val].2 ≤
      inputScale D.input ^ 4 * 2 ^ ((n + 1) / 2) := by
    have hw := CompressionWeights.compact_scale D.input hn D.weights
      ((source D e).compact i) ((hl i).trans (by omega))
    simpa only [compactLists, Vector.getElem_ofFn] using
      hw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (hl i)))
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 7))) => hb i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_assoc] using hs

theorem compact_lengths_source (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (hn : 10000 ≤ n) :
    (∑ i : Fin 7, (compactLists D.weights (source D e))[i.val].1.length) ≤
      7 * 2 ^ ((n + 1) / 2) := by
  have hb (i : Fin 7) : (compactLists D.weights (source D e))[i.val].1.length ≤
      2 ^ ((n + 1) / 2) := by
    rw [compactLists_source]
    have hd := (List.dedup_sublist ((rawWeightList D.weights (D.block e i)).mergeSort
      (fun x y => decide (x ≤ y)))).length_le
    simp only [List.length_mergeSort, rawWeightList_length] at hd
    exact hd.trans (Nat.pow_le_pow_right (by decide) (by
      simpa only [source, Finset.length_sort] using (source_lengths D e hn).1 i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 7))) => hb i)

theorem raw_work_source (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (hn : 10000 ≤ n) :
    (CompressionWeights.raw D.weights (source D e).left).2 +
      (CompressionWeights.raw D.weights ((source D e).right 0)).2 +
      (CompressionWeights.raw D.weights ((source D e).right 1)).2 ≤
        3 * inputScale D.input ^ 3 * 2 ^ ((n + 1) / 2) := by
  have hl := source_lengths D e hn
  have hs (V : List (Fin n)) (hv : V.length ≤ (n + 1) / 2) :
      (CompressionWeights.raw D.weights V).2 ≤ inputScale D.input ^ 3 * 2 ^ ((n + 1) / 2) :=
    (CompressionWeights.raw_scale D.input hn D.weights V (hv.trans (by omega))).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hv))
  have h₀ := hs _ hl.2.1
  have h₁ := hs _ (hl.2.2 0)
  have h₂ := hs _ (hl.2.2 1)
  nlinarith only [h₀, h₁, h₂]

theorem assemble_work_source (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (he : D.compactTests e = true) (hn : 10000 ≤ n) :
    (assemble (compactLists D.weights (source D e))
      (CompressionWeights.raw D.weights (source D e).left).1
      (CompressionWeights.raw D.weights ((source D e).right 0)).1
      (CompressionWeights.raw D.weights ((source D e).right 1)).1).2 ≤
        18 * 2 ^ ((n + 1) / 2) + 13 := by
  let T := 2 ^ ((n + 1) / 2)
  have hc : compressionDictionaryCapacity n ≤ T := by
    unfold compressionDictionaryCapacity T
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hs (i : Fin 4) := D.stored_lists_capacity e he (by omega) i
  have hf (i : Fin 4) := (hs i).1.trans hc
  have hr (i : Fin 4) := (hs i).2.trans hc
  have ha : PreparedCompressionPass.size (PreparedCompressionPass.source D e) ≤ 8 * T + 1 := by
    have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
      show (D.storedFirst e i).length + (D.storedSecond e i).length ≤ 2 * T from by
        have := hf i
        have := hr i
        omega)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hb
    simp only [PreparedCompressionPass.size, PreparedCompressionPass.source, List.size_toArray]
    omega
  have hp (i : Fin 2) : 0 < (rawWeightList D.weights (D.rightRaw e i)).length := by
    rw [rawWeightList_length]
    positivity
  have h₀ := pairSums_work_le (compactWeightList D.weights (D.block e 1))
    (rawWeightList D.weights (D.rightRaw e 0)) (hp 0)
  have h₁ := pairSums_work_le (compactWeightList D.weights (D.block e 3))
    (rawWeightList D.weights (D.rightRaw e 1)) (hp 1)
  have hb₀ : (pairSums (compactWeightList D.weights (D.block e 1))
      (rawWeightList D.weights (D.rightRaw e 0))).2 ≤ 5 * T + 1 :=
    h₀.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 5 (hr 2)) 1)
  have hb₁ : (pairSums (compactWeightList D.weights (D.block e 3))
      (rawWeightList D.weights (D.rightRaw e 1))).2 ≤ 5 * T + 1 :=
    h₁.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 5 (hr 3)) 1)
  change _ + _ + PreparedCompressionPass.size (assemble _ _ _ _).1 + 10 ≤ _
  rw [assemble_source]
  simp only [compactLists, Vector.getElem_ofFn, source, CompressionWeights.compact_source,
    CompressionWeights.raw_source]
  change (pairSums (compactWeightList D.weights (D.block e 1))
      (rawWeightList D.weights (D.rightRaw e 0))).2 +
    (pairSums (compactWeightList D.weights (D.block e 3))
      (rawWeightList D.weights (D.rightRaw e 1))).2 +
    PreparedCompressionPass.size (PreparedCompressionPass.source D e) + 10 ≤ 18 * T + 13
  omega

theorem run_work_source (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (hn : 10000 ≤ n) :
    (run D.weights (source D e) (2 ^ CompressionSetup.executableCapExponent n)).2 ≤
      inputScale D.input ^ 5 * 2 ^ ((n + 1) / 2) := by
  have hc := compact_work_source D e hn
  have hlen := compact_lengths_source D e hn
  have hr := raw_work_source D e hn
  have hu : 10000 ≤ inputScale D.input := by unfold inputScale; omega
  have hp34 : inputScale D.input ^ 3 ≤ inputScale D.input ^ 4 :=
    pow_le_pow_right' (by omega) (by decide)
  have hp4 : 1 ≤ inputScale D.input ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hm : 100 * inputScale D.input ^ 4 ≤ inputScale D.input ^ 5 := by
    calc
      _ ≤ inputScale D.input * inputScale D.input ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hT : 1 ≤ 2 ^ ((n + 1) / 2) := Nat.one_le_two_pow
  have hsmall := Nat.mul_le_mul_right (2 ^ ((n + 1) / 2)) hp4
  have h34 := Nat.mul_le_mul_right (2 ^ ((n + 1) / 2)) hp34
  have hfinal := Nat.mul_le_mul_right (2 ^ ((n + 1) / 2)) hm
  dsimp only [run]
  rw [passed_source]
  simp only [Finset.sum_add_distrib]
  split
  next he =>
    have ha := assemble_work_source D e he hn
    dsimp only
    nlinarith only [hc, hlen, hr, ha, hT, hsmall, h34, hfinal]
  next =>
    dsimp only
    nlinarith only [hc, hlen, hT, hsmall, hfinal]

end LowSpaceSubsetSum.CompressionArrayBuild

end OAI
