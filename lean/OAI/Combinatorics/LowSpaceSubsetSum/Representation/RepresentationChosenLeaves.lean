import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationAllocatedSurvival

namespace OAI

/-! # The chosen solution masks are actual raw leaf occurrences -/

noncomputable section

namespace LowSpaceSubsetSum

def orientedMask {ι : Type*} [DecidableEq ι] (complement : Bool)
    (D A : Finset ι) : Finset ι := if complement then A \ D else D

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def categoryBlockEquiv (z : Layout n) (f : R.Partitions z) (j : Fin 3)
    (C : Finset (Fin n)) (hCM : C ⊆ R.orderedMixers z j) (a : Fin (blockCount j)) :
    ↥(C ∩ R.rawPartitionBlock z f j a.val) ≃
      {x : ↥C // (f j).val ⟨x.val, hCM x.property⟩ = a} where
  toFun x := ⟨⟨x.val, (Finset.mem_inter.mp x.property).1⟩, by
    obtain ⟨_, hx, he⟩ := Finset.mem_filter.mp (Finset.mem_inter.mp x.property).2
    exact Fin.ext he⟩
  invFun x := ⟨x.val.val, Finset.mem_inter.mpr ⟨x.val.property,
    Finset.mem_filter.mpr ⟨hCM x.val.property, hCM x.val.property, congrArg Fin.val x.property⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem prescription_block_card (z : Layout n) (f : R.Partitions z) (j : Fin 3)
    {D : Finset (Fin n)} (hDA : D ⊆ R.selectedHalves z j)
    {q : Fin 3 → Fin (blockCount j) → ℕ}
    (hp : representativePrescriptions hDA (R.selectedHalves_subset z j) q (f j))
    (c : Fin 3) (a : Fin (blockCount j)) :
    ((representativeCategories D (R.selectedHalves z j) (R.orderedMixers z j) c) ∩
      R.rawPartitionBlock z f j a.val).card = q c a := by
  let C := representativeCategories D (R.selectedHalves z j) (R.orderedMixers z j) c
  have hCM : C ⊆ R.orderedMixers z j :=
    representativeCategories_subset hDA (R.selectedHalves_subset z j) c
  have he := Fintype.card_congr (R.categoryBlockEquiv z f j C hCM a)
  have hc := congrFun (hp c) a
  simpa only [Fintype.card_coe, MatchingSmoothing.histogram] using he.trans hc

theorem prescribedMask_block_card (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (j : Fin 3) {D : Finset (Fin n)} (hDA : D ⊆ R.selectedHalves z j)
    (hp : representativePrescriptions hDA (R.selectedHalves_subset z j)
      (representativeBlockProfile (blockCount j) (blockHalf n j) (g j).val) (f j))
    (complement : Bool) (a : Fin (blockCount j)) :
    ((orientedMask complement D (R.selectedHalves z j)) ∩ R.rawPartitionBlock z f j a.val).card =
      if complement then blockHalf n j - balancedBlockCounts (blockCount j) (g j).val a
      else balancedBlockCounts (blockCount j) (g j).val a := by
  cases complement
  · exact R.prescription_block_card z f j hDA hp 0 a
  · exact R.prescription_block_card z f j hDA hp 1 a

/-- The top and local mask components are chosen by the representation;
the background component is the fixed solution restricted to its leaf. -/
def maskLeafOccurrence (z : Layout n) (f : R.Partitions z) (B : Fin n → Fin 2 × Fin 4)
    (D : Fin 3 → Finset (Fin n)) (j : Fin 2) (i : Fin 4) : RepresentationLeaf.Occurrence (Fin n) :=
  ((orientedMask (j != 0) (D 0) (R.selectedHalves z 0) ∩ R.rawPartitionBlock z f 0 i.val,
    orientedMask (decide (2 ≤ i.val)) (D j.succ) (R.selectedHalves z j.succ) ∩
      R.rawPartitionBlock z f j.succ (i.val % 2)),
    z.2 ∩ R.rawBackground z B j i)

theorem maskLeafOccurrence_mem (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (D : Fin 3 → Finset (Fin n))
    (hD : ∀ k, D k ⊆ R.selectedHalves z k)
    (hp : ∀ k, representativePrescriptions (hD k) (R.selectedHalves_subset z k)
      (representativeBlockProfile (blockCount k) (blockHalf n k) (g k).val) (f k))
    (j : Fin 2) (i : Fin 4) :
    R.maskLeafOccurrence z f B D j i ∈ (R.rawLeaf z g f B j i).occurrences := by
  have ht := R.prescribedMask_block_card z g f 0 (hD 0) (hp 0) (j != 0) i
  have hj : blockCount j.succ = 2 := by fin_cases j <;> rfl
  have hbound : i.val % 2 < blockCount j.succ := by rw [hj]; omega
  have hl := R.prescribedMask_block_card z g f j.succ (hD j.succ) (hp j.succ)
    (decide (2 ≤ i.val)) ⟨i.val % 2, hbound⟩
  have ht' : (R.maskLeafOccurrence z f B D j i).1.1.card = (R.rawLeaf z g f B j i).topCount := by
    fin_cases j <;> exact ht
  have hl' : (R.maskLeafOccurrence z f B D j i).1.2.card = (R.rawLeaf z g f B j i).localCount := by
    fin_cases j <;> fin_cases i <;> exact hl
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, ht'⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hl'⟩
  · exact Finset.mem_powerset.mpr Finset.inter_subset_right

theorem chosenLeafOccurrence_mem (B : BackgroundAssignment n) (h : R.PrimeHistory)
    (r : R.Residues h.2) (hr : R.ResidueSuccess (R.actualOffsets B) h r)
    (leafB : Fin n → Fin 2 × Fin 4) (j : Fin 2) (i : Fin 4) :
    R.maskLeafOccurrence h.1.1.1 h.1.2 leafB (R.chosenMasks (R.actualOffsets B) h r) j i ∈
      (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 leafB j i).occurrences := by
  have hm := R.chosenMasks_spec (R.actualOffsets B) hr
  let hD := fun k => (hm k).1
  have hp (k : Fin 3) : representativePrescriptions (hD k) (R.selectedHalves_subset h.1.1.1 k)
      (representativeBlockProfile (blockCount k) (blockHalf n k) (h.1.1.2 k).val) (h.1.2 k) := by
    obtain ⟨_, hp⟩ := (hm k).2.2.2
    exact hp
  exact R.maskLeafOccurrence_mem h.1.1.1 h.1.1.2 h.1.2 leafB _ hD hp j i

def maskParentOccurrence (z : Layout n) (f : R.Partitions z) (B : Fin n → Fin 2 × Fin 4)
    (D : Fin 3 → Finset (Fin n)) (j : Fin 2) : RepresentationUniverse.ParentOccurrence (Fin n) :=
  ((R.maskLeafOccurrence z f B D j 0, R.maskLeafOccurrence z f B D j 1),
    (R.maskLeafOccurrence z f B D j 2, R.maskLeafOccurrence z f B D j 3))

private theorem four_of_pairwise {ι : Type*} [DecidableEq ι] (S : Fin 4 → Finset ι)
    (h : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    RepresentationUniverse.DisjointFour (S 0) (S 1) (S 2) (S 3) :=
  ⟨h 0 1 (by decide), Finset.disjoint_union_left.mpr ⟨h 0 2 (by decide), h 1 2 (by decide)⟩,
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨h 0 3 (by decide), h 1 3 (by decide)⟩, h 2 3 (by decide)⟩⟩

private theorem two_mask_parts_disjoint {ι : Type*} [DecidableEq ι]
    (D A X Y : Finset ι) (hXY : Disjoint X Y) :
    RepresentationUniverse.DisjointFour (D ∩ X) (D ∩ Y) ((A \ D) ∩ X) ((A \ D) ∩ Y) := by
  have h01 : Disjoint (D ∩ X) (D ∩ Y) := hXY.mono Finset.inter_subset_right Finset.inter_subset_right
  have h02 : Disjoint (D ∩ X) ((A \ D) ∩ X) :=
    Finset.disjoint_sdiff.mono Finset.inter_subset_left Finset.inter_subset_left
  have h03 : Disjoint (D ∩ X) ((A \ D) ∩ Y) :=
    hXY.mono Finset.inter_subset_right Finset.inter_subset_right
  have h12 : Disjoint (D ∩ Y) ((A \ D) ∩ X) :=
    hXY.symm.mono Finset.inter_subset_right Finset.inter_subset_right
  have h13 : Disjoint (D ∩ Y) ((A \ D) ∩ Y) :=
    Finset.disjoint_sdiff.mono Finset.inter_subset_left Finset.inter_subset_left
  have h23 : Disjoint ((A \ D) ∩ X) ((A \ D) ∩ Y) :=
    hXY.mono Finset.inter_subset_right Finset.inter_subset_right
  exact ⟨h01, Finset.disjoint_union_left.mpr ⟨h02, h12⟩,
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨h03, h13⟩, h23⟩⟩

theorem maskParentOccurrence_valid (z : Layout n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (D : Fin 3 → Finset (Fin n)) (j : Fin 2) :
    RepresentationUniverse.Valid (R.maskParentOccurrence z f B D j) := by
  refine ⟨?_, ?_, ?_⟩
  · apply four_of_pairwise (fun i => (R.maskLeafOccurrence z f B D j i).1.1)
    intro i i' hi
    exact (R.rawPartitionBlock_disjoint z f 0 (fun he => hi (Fin.ext he))).mono
      Finset.inter_subset_right Finset.inter_subset_right
  · exact two_mask_parts_disjoint (D j.succ) (R.selectedHalves z j.succ)
      (R.rawPartitionBlock z f j.succ 0) (R.rawPartitionBlock z f j.succ 1)
      (R.rawPartitionBlock_disjoint z f j.succ (by decide))
  · apply four_of_pairwise (fun i => (R.maskLeafOccurrence z f B D j i).2)
    intro i i' hi
    exact (R.rawBackground_disjoint z B (fun he => hi (congrArg Prod.snd he))).mono
      Finset.inter_subset_right Finset.inter_subset_right

theorem chosenParentOccurrence_mem (B : BackgroundAssignment n) (h : R.PrimeHistory)
    (r : R.Residues h.2) (hr : R.ResidueSuccess (R.actualOffsets B) h r)
    (leafB : Fin n → Fin 2 × Fin 4) (j : Fin 2) :
    R.maskParentOccurrence h.1.1.1 h.1.2 leafB (R.chosenMasks (R.actualOffsets B) h r) j ∈
      RepresentationUniverse.parents (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 leafB j) := by
  exact (RepresentationUniverse.mem_parents _ _).mpr
    ⟨R.chosenLeafOccurrence_mem B h r hr leafB j 0,
      R.chosenLeafOccurrence_mem B h r hr leafB j 1,
      R.chosenLeafOccurrence_mem B h r hr leafB j 2,
      R.chosenLeafOccurrence_mem B h r hr leafB j 3⟩

theorem chosenEntry_mem (B : BackgroundAssignment n) (h : R.PrimeHistory)
    (r : R.Residues h.2) (hr : R.ResidueSuccess (R.actualOffsets B) h r)
    (leafB : Fin n → Fin 2 × Fin 4) (j : Fin 2) :
    RepresentationUniverse.entry (R.signedWeights h.1.1.1)
      (R.maskParentOccurrence h.1.1.1 h.1.2 leafB (R.chosenMasks (R.actualOffsets B) h r) j) ∈
      RepresentationUniverse.validEntries (R.signedWeights h.1.1.1)
        (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 leafB j) := by
  classical
  exact Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr
    ⟨R.chosenParentOccurrence_mem B h r hr leafB j,
      R.maskParentOccurrence_valid _ _ _ _ _⟩, rfl⟩

end RepresentationSetup

end LowSpaceSubsetSum

end

end OAI
