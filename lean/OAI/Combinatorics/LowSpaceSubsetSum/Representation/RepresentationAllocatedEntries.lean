import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationAllocatedLeaves

namespace OAI

/-! # The actual valid-entry envelope after background allocation -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

open scoped BigOperators

variable {n : ℕ} (R : RepresentationSetup n)

theorem rawBackground_disjoint (z : Layout n) (B : Fin n → Fin 2 × Fin 4)
    {j j' : Fin 2} {i i' : Fin 4} (h : (j, i) ≠ (j', i')) :
    Disjoint (R.rawBackground z B j i) (R.rawBackground z B j' i') := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)

theorem rawLeaf_background_card_sum (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) :
    (RepresentationUniverse.backgroundDomain (R.rawLeaf z g f B j)).card =
      (R.rawLeaf z g f B j 0).background.card + (R.rawLeaf z g f B j 1).background.card +
      (R.rawLeaf z g f B j 2).background.card + (R.rawLeaf z g f B j 3).background.card := by
  have h (i i' : Fin 4) (hi : i ≠ i') :
      Disjoint (R.rawLeaf z g f B j i).background (R.rawLeaf z g f B j i').background :=
    R.rawBackground_disjoint z B (fun he => hi (congrArg Prod.snd he))
  rw [RepresentationUniverse.backgroundDomain,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨h 0 3 (by decide), h 1 3 (by decide)⟩, h 2 3 (by decide)⟩),
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨h 0 2 (by decide), h 1 2 (by decide)⟩),
    Finset.card_union_of_disjoint (h 0 1 (by decide))]

theorem rawLeaf_allocated_backgroundDomain_card (z : Layout n) (g : Guesses n)
    (f : R.Partitions z) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j : Fin 2) :
    (RepresentationUniverse.backgroundDomain
      (R.rawLeaf z g f (R.allocatedBackground z g hn hlog) j)).card =
      representationParentSize n g j := by
  rw [R.rawLeaf_background_card_sum]
  simp_rw [R.rawLeaf_allocated_background_card]
  have h0 := leafBackgroundSize_sum (representationChildSize n g j false)
  have h1 := leafBackgroundSize_sum (representationChildSize n g j true)
  have hc := (representationAllocation_feasible g hn hlog).2 j
  have hs := (allocation_feasible (representationParentSize n g j)
    (representationBits n g false j.succ) (representationBits n g true j.succ) hc.1 hc.2).2
  change leafBackgroundSize (representationChildSize n g j false) 0 +
    leafBackgroundSize (representationChildSize n g j false) 1 +
    leafBackgroundSize (representationChildSize n g j true) 0 +
    leafBackgroundSize (representationChildSize n g j true) 1 = _
  change representationChildSize n g j false + representationChildSize n g j true = _ at hs
  omega

theorem rawLeaf_topCount_sum (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) :
    (R.rawLeaf z g f B j 0).topCount + (R.rawLeaf z g f B j 1).topCount +
      (R.rawLeaf z g f B j 2).topCount + (R.rawLeaf z g f B j 3).topCount =
      representationCount n g (j != 0) 0 := by
  have hs := balancedBlockCounts_sum 4 (g 0).val (by decide)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change balancedBlockCounts 4 (g 0).val 0 + (balancedBlockCounts 4 (g 0).val 1 +
    (balancedBlockCounts 4 (g 0).val 2 + balancedBlockCounts 4 (g 0).val 3)) = (g 0).val at hs
  have hg := (Finset.mem_Icc.mp (g 0).property).2
  have hk : (g 0).val ≤ 4 * blockHalf n 0 := by
    change (g 0).val ≤ 8 * (3 * n / 100) / 4 at hg
    change (g 0).val ≤ 4 * (3 * n / 100)
    omega
  have hle (i : Fin 4) := balancedBlockCounts_le 4 (blockHalf n 0) (g 0).val (Or.inr rfl) hk i
  have hhalf : mixerSize n / 2 = 4 * blockHalf n 0 := by
    change 8 * (3 * n / 100) / 2 = 4 * (3 * n / 100)
    omega
  fin_cases j
  · change balancedBlockCounts 4 (g 0).val 0 + balancedBlockCounts 4 (g 0).val 1 +
      balancedBlockCounts 4 (g 0).val 2 + balancedBlockCounts 4 (g 0).val 3 = (g 0).val
    omega
  · change (blockHalf n 0 - balancedBlockCounts 4 (g 0).val 0) +
      (blockHalf n 0 - balancedBlockCounts 4 (g 0).val 1) +
      (blockHalf n 0 - balancedBlockCounts 4 (g 0).val 2) +
      (blockHalf n 0 - balancedBlockCounts 4 (g 0).val 3) = mixerSize n / 2 - (g 0).val
    have h0 := hle 0
    have h1 := hle 1
    have h2 := hle 2
    have h3 := hle 3
    omega

theorem rawLeaf_allocated_entry_card (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j : Fin 2) :
    ((RepresentationUniverse.validEntries (R.signedWeights z)
      (R.rawLeaf z g f (R.allocatedBackground z g hn hlog) j)).card : ℝ) ≤
      (2 : ℝ) ^ (representationEntropy n g (j != 0) 0 + representationParentSize n g j +
        ((mixerSize n : ℝ) - deficiency (R.signedWeights z) (R.orderedMixers z j.succ))) := by
  let B := R.allocatedBackground z g hn hlog
  have htop : (RepresentationUniverse.topDomain (R.rawLeaf z g f B j)).card = mixerSize n := by
    rw [R.rawLeaf_topDomain, R.orderedMixers_card_mixerSize]
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have he := RepresentationMoments.entry_card_entropy (R.signedWeights z) (R.rawLeaf z g f B j)
    (R.rawLeaf_top_disjoint z g f B j) (by
      rw [R.rawLeaf_topCount_sum, htop]
      exact representationCount_le n g (j != 0) 0)
  rw [R.rawLeaf_topCount_sum, htop, representationCount_fraction g (j != 0) hm,
    R.rawLeaf_allocated_backgroundDomain_card, R.rawLeaf_mixerDomain,
    R.orderedMixers_card_mixerSize] at he
  exact he

/-- The entire deterministic entry-allocation loss is at most two plus one
binary logarithm. The local distinct-sum factor is retained exactly. -/
theorem rawLeaf_allocated_entry_card_bound (z : Layout n) (g : Guesses n)
    (f : R.Partitions z) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j : Fin 2) :
    ((RepresentationUniverse.validEntries (R.signedWeights z)
      (R.rawLeaf z g f (R.allocatedBackground z g hn hlog) j)).card : ℝ) ≤
      (2 : ℝ) ^ ((representationBackgroundSize n : ℝ) / 2 +
        (representationEntropy n g false 0 + representationEntropy n g true 0) / 2 +
        (mixerSize n : ℝ) - deficiency (R.signedWeights z) (R.orderedMixers z j.succ) +
        Real.logb 2 ((mixerSize n : ℝ) + 1) + 2) := by
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  have h0 := (representationAllocation_feasible g hn hlog).1
  have hb := weighted_parent_allocation_bound (j != 0) (representationBackgroundSize n)
    (representationBits n g false 0) (representationBits n g true 0) h0.1 h0.2
    (representationBits_entropy_error g false hm 0).le
    (representationBits_entropy_error g true hm 0).le
  have hs : representationEntropy n g (j != 0) 0 =
      (if j != 0 then representationEntropy n g true 0 else representationEntropy n g false 0) := by
    cases h : (j != 0) <;> simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← hs] at hb
  apply (R.rawLeaf_allocated_entry_card z g f hn hlog j).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  change representationEntropy n g (j != 0) 0 +
    (representationParentSize n g j : ℝ) ≤ _ at hb
  linarith

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
