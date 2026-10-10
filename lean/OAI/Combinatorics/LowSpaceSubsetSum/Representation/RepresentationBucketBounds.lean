import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationExtraPrime
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionSurvival
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Buckets

namespace OAI

/-! # Deterministic capacity bounds for the designated representation buckets -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- The executable spread test bounds every deficiency difference. -/
theorem spread_deficiency_difference (z : Layout n)
    (hs : mixerSpreadTest (R.signedWeights z) (R.orderedMixers z) n) (i j : Fin 3) :
    deficiency R.originalWeights (R.orderedMixers z j) -
      deficiency R.originalWeights (R.orderedMixers z i) ≤ (n : ℝ) / 2000 := by
  have h : (distinctSumCount (R.signedWeights z) (R.orderedMixers z i) : ℝ) ≤
      distinctSumCount (R.signedWeights z) (R.orderedMixers z j) * (2 : ℝ) ^ (n / 2000) := by
    exact_mod_cast hs i j
  rw [← two_pow_card_sub_deficiency, ← two_pow_card_sub_deficiency,
    ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)] at h
  have he := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h
  simp only [R.orderedMixers_card_mixerSize, signedWeights, deficiency_flip] at he
  have hf : ((n / 2000 : ℕ) : ℝ) ≤ (n : ℝ) / 2000 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2000)).mpr
    exact_mod_cast Nat.div_mul_le_self n 2000
  linarith

/-- The numerical extra-prime margin is derived from the actual spread test. -/
theorem extraPrime_entry_gap (z : Layout n) (g : Guesses n) (hn : 10000 ≤ n)
    (hs : mixerSpreadTest (R.signedWeights z) (R.orderedMixers z) n) :
    (3 / 2000 : ℝ) * n ≤ R.extraPrimeRate z -
      (R.resourceLambda z g - (199 / 1000 : ℝ) * n) := by
  let d := min (deficiency R.originalWeights (R.orderedMixers z 1))
    (deficiency R.originalWeights (R.orderedMixers z 2))
  have hf0 : R.filterDeficit z 0 ≤ d / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply le_min
    · have h := (R.filterDeficit_mono z (by decide : (0 : Fin 3) ≤ 1)).trans
        (min_le_right _ _)
      change R.filterDeficit z 0 ≤ deficiency R.originalWeights (R.orderedMixers z 1) / 2 at h
      linarith
    · have h := (R.filterDeficit_mono z (by decide : (0 : Fin 3) ≤ 2)).trans
        (min_le_right _ _)
      change R.filterDeficit z 0 ≤ deficiency R.originalWeights (R.orderedMixers z 2) / 2 at h
      linarith
  have hf2 : R.filterDeficit z 2 ≤ d / 2 + (n : ℝ) / 4000 := by
    have hd := R.spread_deficiency_difference z hs 1 2
    have hf : R.filterDeficit z 2 ≤ deficiency R.originalWeights (R.orderedMixers z 2) / 2 :=
      min_le_right _ _
    dsimp only [d]
    rcases le_total (deficiency R.originalWeights (R.orderedMixers z 1))
      (deficiency R.originalWeights (R.orderedMixers z 2)) with h | h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      linarith [Nat.cast_nonneg n (α := ℝ)]
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have hg := guess_density g hm 0
  have hp := binaryEntropy_pair_le_quarter
    (p := ((g 0).val : ℝ) / mixerSize n) (by linarith [hg.1]) (by linarith [hg.2])
  have hh : representationHbar n g ≤ binaryEntropy (1 / 4) := by
    unfold representationHbar
    linarith
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  exact bucket_exponent_gap n (mixerSize n) (binaryEntropy (1 / 4))
    (representationHbar n g) d (R.filterDeficit z 0) (R.filterDeficit z 2)
    hnR (mixerSize_bounds n).1.le binaryEntropy_quarter_lt.le hh hf0 hf2

/-- The main-branch bit-scale test absorbs the entire polynomial collision
loss, with the actual rounded capacity and the strict exponent margin. -/
theorem representation_bucket_loss (z : Layout n) (g : Guesses n) (hn : 20000 ≤ n)
    (hs : mixerSpreadTest (R.signedWeights z) (R.orderedMixers z) n)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) :
    4 * (inputScale R.input : ℝ) ^ 203 *
      (2 : ℝ) ^ (R.resourceLambda z g - R.extraPrimeRate z) /
        (compressionDictionaryCapacity n : ℝ) ≤ 1 / 10 := by
  have hu : (0 : ℝ) < inputScale R.input := by
    exact_mod_cast (show 0 < inputScale R.input by unfold inputScale; omega)
  have hu203 : (inputScale R.input : ℝ) ^ 203 =
      (2 : ℝ) ^ (203 * Real.logb 2 (inputScale R.input : ℝ)) := by
    have h := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)
      (Real.logb 2 (inputScale R.input : ℝ)) 203
    rw [Real.rpow_logb (by norm_num) (by norm_num) hu] at h
    simpa only [Nat.cast_ofNat, mul_comm] using h.symm
  have hgap := R.extraPrime_entry_gap z g (by omega) hs
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnum : 4 * (inputScale R.input : ℝ) ^ 203 *
      (2 : ℝ) ^ (R.resourceLambda z g - R.extraPrimeRate z) ≤
        (2 : ℝ) ^ ((199 / 1000 : ℝ) * n - 5) := by
    calc
      _ = (2 : ℝ) ^ ((2 + 203 * Real.logb 2 (inputScale R.input : ℝ)) +
          (R.resourceLambda z g - R.extraPrimeRate z)) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), ← hu203]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h16 : 16 * (2 : ℝ) ^ ((199 / 1000 : ℝ) * n - 5) =
      (2 : ℝ) ^ ((199 / 1000 : ℝ) * n - 1) := by
    rw [show (199 / 1000 : ℝ) * n - 1 = 4 + ((199 / 1000 : ℝ) * n - 5) by ring,
      Real.rpow_add (by norm_num)]
    norm_num
  have hC := compression_capacity_lower n
  have hpos : (0 : ℝ) < compressionDictionaryCapacity n := by
    exact_mod_cast (show 0 < compressionDictionaryCapacity n by
      unfold compressionDictionaryCapacity; positivity)
  apply (div_le_iff₀ hpos).mpr
  nlinarith


/-- Every actual valid entry retains the prescribed top-mask size. -/
theorem rawEntry_mask_spec (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) (e : Entry (Fin n))
    (he : e ∈ RepresentationUniverse.validEntries (R.signedWeights z) (R.rawLeaf z g f B j)) :
    e.mask ⊆ R.orderedMixers z 0 ∧ e.mask.card = representationCount n g (j != 0) 0 := by
  classical
  let : DecidablePred (RepresentationUniverse.Valid (ι := Fin n)) :=
    fun _ => Classical.propDecidable _
  let : DecidableEq (Entry (Fin n)) := fun _ _ => Classical.propDecidable _
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hx, _⟩ := Finset.mem_filter.mp hx
  have ht := (RepresentationUniverse.parent_part_subsets _ hx).1
  have hc := RepresentationUniverse.topMask_card (R.rawLeaf z g f B j)
    (R.rawLeaf_top_disjoint z g f B j) hx
  rw [R.rawLeaf_topDomain] at ht
  rw [R.rawLeaf_topCount_sum] at hc
  exact ⟨ht, hc⟩

/-- The equal-weight exponent on the left is bounded by `.194736 n`. -/
theorem left_equalWeight_bound (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (hn : 100 ≤ n) (X : Finset (Entry (Fin n)))
    (hX : X ⊆ RepresentationUniverse.validEntries (R.signedWeights z) (R.rawLeaf z g f B 0))
    (x : Entry (Fin n)) :
    ((sameWeightKeys X Entry.value x).card : ℝ) ≤
      (2 : ℝ) ^ ((24342 / 125000 : ℝ) * n) := by
  have hc := same_weight_card_le_choose X (R.orderedMixers z 0) (g 0).val (by
    intro e he
    exact R.rawEntry_mask_spec z g f B 0 e (hX he)) x.value
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have hg := guess_density g hm 0
  have hgN : (g 0).val ≤ mixerSize n := representationCount_le n g false 0
  have he := (choose_entropy_bounds (mixerSize n) (g 0).val hgN).2
  have hh : binaryEntropy (((g 0).val : ℝ) / mixerSize n) ≤ binaryEntropy (1 / 4) :=
    binaryEntropy_monoOn ⟨by linarith [hg.1], by linarith [hg.2]⟩
      (by constructor <;> norm_num) hg.2
  have hprod := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (mixerSize n) (α := ℝ))
  have hnum : (mixerSize n : ℝ) * binaryEntropy (((g 0).val : ℝ) / mixerSize n) ≤
      (24342 / 125000 : ℝ) * n := by
    have hq := mul_le_mul_of_nonneg_left binaryEntropy_quarter_lt.le
      (Nat.cast_nonneg (mixerSize n) (α := ℝ))
    nlinarith [(mixerSize_bounds n).2]
  apply (show ((sameWeightKeys X Entry.value x).card : ℝ) ≤
      ((mixerSize n).choose (g 0).val : ℝ) by
    rw [R.orderedMixers_card_mixerSize] at hc
    exact_mod_cast hc).trans
  exact he.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hnum)

/-- The actual rounded dictionary capacity leaves half its space for equal
weights in the left solution bucket. -/
theorem left_equalWeight_half_capacity (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (hn : 1000 ≤ n) (X : Finset (Entry (Fin n)))
    (hX : X ⊆ RepresentationUniverse.validEntries (R.signedWeights z) (R.rawLeaf z g f B 0))
    (x : Entry (Fin n)) :
    ((sameWeightKeys X Entry.value x).card : ℝ) ≤ (compressionDictionaryCapacity n : ℝ) / 2 := by
  have hc := R.left_equalWeight_bound z g f B (by omega) X hX x
  have hC := compression_capacity_lower n
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 2 * (2 : ℝ) ^ ((24342 / 125000 : ℝ) * n) ≤
      (2 : ℝ) ^ ((199 / 1000 : ℝ) * n - 1) := by
    calc
      _ = (2 : ℝ) ^ ((24342 / 125000 : ℝ) * n + 1) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith

/-- At a full right-mask prefix, at most one exact key has the chosen weight. -/
theorem right_fullMask_half_capacity (X : Finset (Entry (Fin n))) (w : ℤ)
    (D : Finset (Fin n)) (hn : 1000 ≤ n) :
    ((X.filter fun e => e.value = w ∧ e.mask = D).card : ℝ) ≤
      (compressionDictionaryCapacity n : ℝ) / 2 := by
  have hc := full_mask_same_weight_card_le_one X w D
  have hC : 2 ≤ compressionDictionaryCapacity n := by
    unfold compressionDictionaryCapacity
    have hk : 1 ≤ 199 * n / 1000 := by omega
    exact (show 2 ^ 1 ≤ 2 ^ (199 * n / 1000) from Nat.pow_le_pow_right (by decide) hk)
  have hcR : ((X.filter fun e => e.value = w ∧ e.mask = D).card : ℝ) ≤ 1 := by exact_mod_cast hc
  have hCR : (2 : ℝ) ≤ compressionDictionaryCapacity n := by exact_mod_cast hC
  linarith

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
