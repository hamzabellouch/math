import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleQueries

namespace OAI

/-! # All-outcome representation leaf and tournament storage bounds -/

noncomputable section

namespace LowSpaceSubsetSum

namespace RepresentationPairData

variable {n : ℕ} (D : RepresentationPairData n)

theorem leftArray_size_le : D.leftArray.size ≤ D.left.occurrences.card := by
  simpa only [leftArray, List.size_toArray, RepresentationLeaf.enumerate_length] using
    List.length_filter_le D.acceptLeft D.left.enumerate

theorem rightArray_size_le : D.rightArray.size ≤ D.right.occurrences.card := by
  simpa only [rightArray, List.size_toArray, RepresentationLeaf.enumerate_length] using
    List.length_filter_le D.acceptRight D.right.enumerate

theorem storedRight_size_le : D.storedRight.size ≤ D.right.occurrences.card := by
  rw [storedRight, ResidueSort.size]
  exact D.rightArray_size_le

theorem reader_comparisons_le (s : D.State) :
    MergedReader.advanceComparisons
      (FilteredStream.key D.wl D.wl D.modulus D.mode)
      (FilteredStream.view D.storedRight) s ≤ Nat.clog 2 D.leftArray.size :=
  MergedReader.advanceComparisons_le _ _ _

end RepresentationPairData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- The main guard absorbs the allocation's polynomial factor with strict
slack below both the tie-buffer and dictionary rates. No survival or resource
event is used. -/
theorem rawLeaf_main_card (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (j : Fin 2) (i : Fin 4) :
    ((R.rawLeaf z g f (R.allocatedBackground z g hn hlog) j i).occurrences.card : ℝ) ≤
      (2 : ℝ) ^ ((37 / 200 : ℝ) * n) := by
  have hu : (0 : ℝ) < inputScale R.input := by
    exact_mod_cast (show 0 < inputScale R.input by unfold inputScale; omega)
  have hraw := R.rawLeaf_allocated_card z g f hn hlog (u := (inputScale R.input : ℝ))
    (by exact_mod_cast (show 2 ≤ inputScale R.input by unfold inputScale; omega))
    (by exact_mod_cast R.mixerSize_add_one_le_scale) j i
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have hb := leaf_exponent n (mixerSize n) (binaryEntropy (1 / 4)) (representationBeta n g j)
    (Nat.cast_nonneg _) (mixerSize_bounds n).2 binaryEntropy_quarter_lt.le
    (representationBeta_upper g hm j)
  have hp : (inputScale R.input : ℝ) ^ 10 =
      (2 : ℝ) ^ (10 * Real.logb 2 (inputScale R.input : ℝ)) := by
    have hh := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)
      (Real.logb 2 (inputScale R.input : ℝ)) 10
    rw [Real.rpow_logb (by norm_num) (by norm_num) hu] at hh
    simpa only [Nat.cast_ofNat, mul_comm] using hh.symm
  calc
    _ ≤ (inputScale R.input : ℝ) ^ 10 * (2 : ℝ) ^ (representationBeta n g j / 2) := hraw
    _ = (2 : ℝ) ^ (10 * Real.logb 2 (inputScale R.input : ℝ) + representationBeta n g j / 2) := by
      rw [hp, Real.rpow_add (by norm_num)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      linarith [Nat.cast_nonneg n (α := ℝ)])

/-- Every prefix and every full-residue counter uses leaf arrays and a
tournament bounded by the same raw-leaf size, even on failed trials. -/
theorem schedule_pair_storage (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (q : ℕ) (hq : 0 < q) (z : ℕ) (side : Fin 2) (P : MaskRestriction n) (child : Fin 2) :
    let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
    (D.leftArray.size : ℝ) ≤ (2 : ℝ) ^ ((37 / 200 : ℝ) * n) ∧
      (D.storedRight.size : ℝ) ≤ (2 : ℝ) ^ ((37 / 200 : ℝ) * n) ∧
      (Tournament.nodes D.start.tree : ℝ) + 1 ≤
        4 * ((2 : ℝ) ^ ((37 / 200 : ℝ) * n) + 1) := by
  dsimp only
  let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
  have hl := R.rawLeaf_main_card h.1.1.1 h.1.1.2 h.1.2 hn hlog hscale side
    ⟨2 * child.val, by omega⟩
  have hr := R.rawLeaf_main_card h.1.1.1 h.1.1.2 h.1.2 hn hlog hscale side
    ⟨2 * child.val + 1, by omega⟩
  have hleft0 : (D.leftArray.size : ℝ) ≤ D.left.occurrences.card := by
    exact_mod_cast D.leftArray_size_le
  have hright0 : (D.storedRight.size : ℝ) ≤ D.right.occurrences.card := by
    exact_mod_cast D.storedRight_size_le
  have hleft := hleft0.trans hl
  have hright := hright0.trans hr
  refine ⟨hleft, hright, ?_⟩
  have ht : (Tournament.nodes D.start.tree : ℝ) + 1 ≤ 4 * ((D.leftArray.size : ℝ) + 1) := by
    exact_mod_cast D.state_nodes
  linarith only [ht, hleft]

theorem schedule_pair_index_bits (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (q : ℕ) (hq : 0 < q) (z : ℕ) (side : Fin 2) (P : MaskRestriction n) (child : Fin 2) :
    let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
    Nat.clog 2 D.leftArray.size ≤ n ∧ FilteredStream.steps D.storedRight.size ≤ n + 1 := by
  dsimp only
  let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
  have hs := R.schedule_pair_storage h r hn hlog hscale q hq z side P child
  have he : (2 : ℝ) ^ ((37 / 200 : ℝ) * n) ≤ (2 : ℝ) ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      linarith [Nat.cast_nonneg n (α := ℝ)])
  have hl : D.leftArray.size ≤ 2 ^ n := by exact_mod_cast hs.1.trans he
  have hr : D.storedRight.size ≤ 2 ^ n := by exact_mod_cast hs.2.1.trans he
  have hleft := FilteredStream.steps_le_index_bits D.leftArray.size n hl
  exact ⟨show Nat.clog 2 D.leftArray.size ≤ n from by
    unfold FilteredStream.steps at hleft
    omega,
    FilteredStream.steps_le_index_bits D.storedRight.size n hr⟩

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
