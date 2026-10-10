import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResourceMoments
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BackgroundDomains
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.LeafAllocationBounds

namespace OAI

/-! # Actual cardinalities of the representation leaf domains -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- The set-level filter is exactly the corresponding fiber of the sampled
balanced coloring. -/
def rawBlockFiberEquiv (z : Layout n) (f : R.Partitions z) (j : Fin 3)
    (a : Fin (blockCount j)) :
    ↥(R.rawPartitionBlock z f j a.val) ≃
      {x : ↥(R.orderedMixers z j) // (f j).val x = a} where
  toFun x := ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩, by
    apply Fin.ext
    obtain ⟨hx, hv⟩ := (Finset.mem_filter.mp x.property).2
    exact hv⟩
  invFun x := ⟨x.val.val, Finset.mem_filter.mpr
    ⟨x.val.property, x.val.property, congrArg Fin.val x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rawPartitionBlock_card (z : Layout n) (f : R.Partitions z) (j : Fin 3)
    (a : Fin (blockCount j)) :
    (R.rawPartitionBlock z f j a.val).card = 2 * blockHalf n j := by
  have he := Fintype.card_congr (R.rawBlockFiberEquiv z f j a)
  have hc := congrFun (f j).property a
  simpa only [Fintype.card_coe, MatchingSmoothing.histogram] using he.trans hc

theorem rawPartitionBlock_biUnion (z : Layout n) (f : R.Partitions z) (j : Fin 3) :
    Finset.univ.biUnion (fun a : Fin (blockCount j) => R.rawPartitionBlock z f j a.val) =
      R.orderedMixers z j := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hx
    exact R.rawPartitionBlock_subset z f j a.val ha
  · intro hx
    apply Finset.mem_biUnion.mpr
    exact ⟨(f j).val ⟨x, hx⟩, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, hx, rfl⟩⟩

theorem rawLeaf_top_card (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) (i : Fin 4) :
    (R.rawLeaf z g f B j i).top.card = 2 * blockHalf n 0 :=
  R.rawPartitionBlock_card z f 0 i

theorem rawLeaf_local_card (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) (i : Fin 4) :
    (R.rawLeaf z g f B j i).mixer.card = 2 * blockHalf n j.succ := by
  have hbound : i.val % 2 < blockCount j.succ := by
    have hb : blockCount j.succ = 2 := by fin_cases j <;> rfl
    rw [hb]
    exact Nat.mod_lt i.val (by decide : 0 < 2)
  exact R.rawPartitionBlock_card z f j.succ ⟨i.val % 2, hbound⟩


theorem rawLeaf_topDomain (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) :
    RepresentationUniverse.topDomain (R.rawLeaf z g f B j) = R.orderedMixers z 0 := by
  have h := R.rawPartitionBlock_biUnion z f 0
  change (Finset.univ : Finset (Fin 4)).biUnion
    (fun a => R.rawPartitionBlock z f 0 a.val) = R.orderedMixers z 0 at h
  rw [← h]
  ext x
  simp [RepresentationUniverse.topDomain, rawLeaf, Fin.exists_fin_succ]

theorem rawLeaf_mixerDomain (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) :
    RepresentationUniverse.mixerDomain (R.rawLeaf z g f B j) = R.orderedMixers z j.succ := by
  have h := R.rawPartitionBlock_biUnion z f j.succ
  fin_cases j
  · change (Finset.univ : Finset (Fin 2)).biUnion
      (fun a => R.rawPartitionBlock z f 1 a.val) = R.orderedMixers z 1 at h
    change RepresentationUniverse.mixerDomain (R.rawLeaf z g f B 0) = R.orderedMixers z 1
    rw [← h]
    ext x
    simp [RepresentationUniverse.mixerDomain, rawLeaf, Fin.exists_fin_succ]
    tauto
  · change (Finset.univ : Finset (Fin 2)).biUnion
      (fun a => R.rawPartitionBlock z f 2 a.val) = R.orderedMixers z 2 at h
    change RepresentationUniverse.mixerDomain (R.rawLeaf z g f B 1) = R.orderedMixers z 2
    rw [← h]
    ext x
    simp [RepresentationUniverse.mixerDomain, rawLeaf, Fin.exists_fin_succ]
    tauto

theorem rawLeaf_topCount_bound (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) (i : Fin 4) :
    (R.rawLeaf z g f B j i).topCount ≤ (R.rawLeaf z g f B j i).top.card := by
  have hg := (Finset.mem_Icc.mp (g 0).property).2
  change (g 0).val ≤ mixerSize n / 4 at hg
  have hk : (g 0).val ≤ 4 * blockHalf n 0 := by
    simp only [mixerSize, blockHalf, Matrix.cons_val_zero] at hg ⊢
    omega
  have hc := balancedBlockCounts_le 4 (blockHalf n 0) (g 0).val (Or.inr rfl) hk i
  rw [R.rawLeaf_top_card]
  change (if j = 0 then balancedBlockCounts 4 (g 0).val i else
    blockHalf n 0 - balancedBlockCounts 4 (g 0).val i) ≤ 2 * blockHalf n 0
  split_ifs <;> omega

theorem rawLeaf_localCount_bound (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) (i : Fin 4) :
    (R.rawLeaf z g f B j i).localCount ≤ (R.rawLeaf z g f B j i).mixer.card := by
  have hg := (Finset.mem_Icc.mp (g j.succ).property).2
  change (g j.succ).val ≤ mixerSize n / 4 at hg
  have hk : (g j.succ).val ≤ 2 * blockHalf n j.succ := by
    have hb : blockHalf n j.succ = 2 * (3 * n / 100) := by fin_cases j <;> rfl
    rw [hb]
    simp only [mixerSize] at hg
    omega
  have hc := balancedBlockCounts_le 2 (blockHalf n j.succ) (g j.succ).val (Or.inl rfl) hk
    ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
  rw [R.rawLeaf_local_card]
  change (if i.val < 2 then balancedBlockCounts 2 (g j.succ).val _ else
    blockHalf n j.succ - balancedBlockCounts 2 (g j.succ).val _) ≤ 2 * blockHalf n j.succ
  split_ifs <;> omega

end RepresentationSetup

/-- Balanced block counts differ from their rational ideal by at most one. -/
theorem balancedBlockCounts_error (l k : ℕ) (hl : 0 < l) (j : Fin l) :
    |(balancedBlockCounts l k j : ℝ) - (k : ℝ) / l| ≤ 1 := by
  have hr := Nat.mod_lt k hl
  have he := Nat.div_add_mod k l
  have heR : (l : ℝ) * (k / l : ℕ) + (k % l : ℕ) = k := by exact_mod_cast he
  have hrR : (k % l : ℕ) < (l : ℝ) := by exact_mod_cast hr
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hd0 : ((k / l : ℕ) : ℝ) ≤ (k : ℝ) / l := by
    apply (le_div_iff₀ hlR).mpr
    nlinarith [show (0 : ℝ) ≤ (k % l : ℕ) from Nat.cast_nonneg _]
  have hd1 : (k : ℝ) / l ≤ (k / l : ℕ) + 1 := by
    apply (div_le_iff₀ hlR).mpr
    nlinarith
  simp only [balancedBlockCounts]
  split_ifs <;> push_cast <;> apply abs_le.mpr <;> constructor <;> linarith

end LowSpaceSubsetSum

end

end OAI
