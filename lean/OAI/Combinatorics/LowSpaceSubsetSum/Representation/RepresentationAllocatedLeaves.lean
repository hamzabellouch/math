import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationAllocation

namespace OAI

/-! # Leaf bounds for the actual computed background partition -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
open RepresentationSetup

def representationBeta (n : ℕ) (g : Guesses n) (j : Fin 2) : ℝ :=
  (representationBackgroundSize n : ℝ) / 4 +
    (representationEntropy n g false 0 + representationEntropy n g true 0) / 4 +
    (representationEntropy n g false j.succ + representationEntropy n g true j.succ) / 2

theorem representationLeafCounts_eq (n : ℕ) (g : Guesses n) (j : Fin 2) (i : Fin 4) :
    representationLeafCounts n g ⟨4 * j.val + i.val, by omega⟩ =
      leafBackgroundSize (representationChildSize n g j (decide (2 ≤ i.val)))
        ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ := by
  fin_cases j <;> fin_cases i <;> rfl

theorem representationBackgroundSize_cast (n : ℕ) :
    (representationBackgroundSize n : ℝ) = n - 3 * (mixerSize n : ℝ) := by
  have hm := (mixerSize_bounds n).2
  have hthreeR : (3 : ℝ) * mixerSize n ≤ n := by linarith
  have hthree : 3 * mixerSize n ≤ n := by exact_mod_cast hthreeR
  simp only [representationBackgroundSize, Nat.cast_sub hthree, Nat.cast_mul, Nat.cast_ofNat]

theorem representationEntropy_pair_le {n : ℕ} (g : Guesses n)
    (hm : 0 < mixerSize n) (j : Fin 3) :
    representationEntropy n g false j + representationEntropy n g true j ≤
      2 * (mixerSize n : ℝ) * binaryEntropy (1 / 4) := by
  have hp := guess_density g hm j
  have h := binaryEntropy_pair_le_quarter (show 0 ≤ ((g j).val : ℝ) / mixerSize n by linarith [hp.1])
    (show ((g j).val : ℝ) / mixerSize n ≤ 1 / 2 by linarith [hp.2])
  have he := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (mixerSize n) (α := ℝ))
  simp only [representationEntropy, orientedDensity, Bool.false_eq_true, ↓reduceIte]
  nlinarith

theorem representationBeta_upper {n : ℕ} (g : Guesses n)
    (hm : 0 < mixerSize n) (j : Fin 2) :
    representationBeta n g j ≤ (n : ℝ) / 4 +
      (-3 / 4 + 3 / 2 * binaryEntropy (1 / 4)) * mixerSize n := by
  have h0 := representationEntropy_pair_le g hm 0
  have hj := representationEntropy_pair_le g hm j.succ
  unfold representationBeta
  rw [representationBackgroundSize_cast]
  nlinarith

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem orderedMixers_card_mixerSize (z : Layout n) (j : Fin 3) :
    (R.orderedMixers z j).card = mixerSize n := by
  rw [R.orderedMixers_card, R.halfSize_eq]
  unfold mixerSize
  omega

theorem mixerUnion_card (z : Layout n) : (R.mixerUnion z).card = 3 * mixerSize n := by
  have h01 := R.orderedMixers_disjoint z (by decide : (0 : Fin 3) ≠ 1)
  have h02 := R.orderedMixers_disjoint z (by decide : (0 : Fin 3) ≠ 2)
  have h12 := R.orderedMixers_disjoint z (by decide : (1 : Fin 3) ≠ 2)
  rw [mixerUnion, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h02, h12⟩),
    Finset.card_union_of_disjoint h01, R.orderedMixers_card_mixerSize,
    R.orderedMixers_card_mixerSize, R.orderedMixers_card_mixerSize]
  omega

theorem backgroundDomain_card (z : Layout n) :
    (Finset.univ \ R.mixerUnion z).card = representationBackgroundSize n := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, R.mixerUnion_card]
  rfl

/-- The background coloring used by the finite program, in its fixed sorted order. -/
def allocatedBackground (z : Layout n) (g : Guesses n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    Fin n → Fin 2 × Fin 4 :=
  backgroundPairColor (Finset.univ \ R.mixerUnion z) (representationLeafCounts n g)
    ((representationLeafCounts_sum g hn hlog).trans (R.backgroundDomain_card z).symm)

theorem rawLeaf_allocated_background_card (z : Layout n) (g : Guesses n)
    (f : R.Partitions z) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (j : Fin 2) (i : Fin 4) :
    (R.rawLeaf z g f (R.allocatedBackground z g hn hlog) j i).background.card =
      leafBackgroundSize (representationChildSize n g j (decide (2 ≤ i.val)))
        ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ := by
  change ((Finset.univ \ R.mixerUnion z).filter fun x =>
    backgroundPairColor _ (representationLeafCounts n g) _ x = (j, i)).card = _
  rw [backgroundPairColor_card, representationLeafCounts_eq]

theorem rawLeaf_allocated_entropy (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    {u : ℝ} (hu : 2 ≤ u) (hmu : (mixerSize n : ℝ) + 1 ≤ u) (j : Fin 2) (i : Fin 4) :
    let L := R.rawLeaf z g f (R.allocatedBackground z g hn hlog) j i
    (L.top.card : ℝ) * binaryEntropy ((L.topCount : ℝ) / L.top.card) +
      (L.mixer.card : ℝ) * binaryEntropy ((L.localCount : ℝ) / L.mixer.card) +
      L.background.card ≤ representationBeta n g j / 2 + Real.logb 2 (u ^ 10) := by
  let B := R.allocatedBackground z g hn hlog
  have hm : 0 < mixerSize n := by unfold mixerSize; omega
  obtain ⟨h0, hchild⟩ := representationAllocation_feasible g hn hlog
  have he (side : Bool) (k : Fin 3) :=
    (representationBits_entropy_error g side hm k).le
  have htop := R.rawLeaf_top_entropy z g f B (by omega) j i
  change _ ≤ representationEntropy n g (j != 0) 0 / 4 + 3 at htop
  have hlocal := R.rawLeaf_local_entropy z g f B (by omega) j i
  change _ ≤ representationEntropy n g (decide (2 ≤ i.val)) j.succ / 2 + 3 at hlocal
  have htop' : ((R.rawLeaf z g f B j i).top.card : ℝ) *
      binaryEntropy ((R.rawLeaf z g f B j i).topCount /
        ((R.rawLeaf z g f B j i).top.card : ℝ)) ≤
      (if j != 0 then representationEntropy n g true 0 else
      representationEntropy n g false 0) / 4 + 3 := by
    cases h : (j != 0) <;> simpa only [h, Bool.false_eq_true, ↓reduceIte] using htop
  have hlocal' : ((R.rawLeaf z g f B j i).mixer.card : ℝ) *
      binaryEntropy ((R.rawLeaf z g f B j i).localCount /
        ((R.rawLeaf z g f B j i).mixer.card : ℝ)) ≤
      (if decide (2 ≤ i.val) then representationEntropy n g true j.succ else
      representationEntropy n g false j.succ) / 2 + 3 := by
    cases h : decide (2 ≤ i.val) <;> simpa only [h, Bool.false_eq_true, ↓reduceIte] using hlocal
  have hbound := allocated_leaf_entropy_bound (j != 0) (decide (2 ≤ i.val))
    ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ (representationBackgroundSize n)
    (representationBits n g false 0) (representationBits n g true 0)
    (representationBits n g false j.succ) (representationBits n g true j.succ)
    h0.1 h0.2 (hchild j).1 (hchild j).2 (he false 0) (he true 0)
    (he false j.succ) (he true j.succ) htop' hlocal'
  have habs := allocated_leaf_error_absorbed hu (Nat.cast_nonneg (mixerSize n)) hmu
  have hbg := R.rawLeaf_allocated_background_card z g f hn hlog j i
  dsimp only [representationChildSize, representationParentSize] at hbg
  dsimp only
  change _ + _ + (leafBackgroundSize _ _ : ℝ) ≤ _ at hbound
  rw [← hbg] at hbound
  dsimp only [B] at hbound
  dsimp only [representationBeta]
  linarith

theorem rawLeaf_allocated_card (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    {u : ℝ} (hu : 2 ≤ u) (hmu : (mixerSize n : ℝ) + 1 ≤ u) (j : Fin 2) (i : Fin 4) :
    ((R.rawLeaf z g f (R.allocatedBackground z g hn hlog) j i).occurrences.card : ℝ) ≤
      u ^ 10 * (2 : ℝ) ^ (representationBeta n g j / 2) := by
  apply RepresentationMoments.leaf_card_of_allocation _
    (R.rawLeaf_topCount_bound z g f _ j i) (R.rawLeaf_localCount_bound z g f _ j i)
    (by linarith : 0 < u)
  exact R.rawLeaf_allocated_entropy z g f hn hlog hu hmu j i

end RepresentationSetup

end LowSpaceSubsetSum

end

end OAI
