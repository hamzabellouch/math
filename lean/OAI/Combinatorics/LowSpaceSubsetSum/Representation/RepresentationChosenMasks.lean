import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationChosenLeaves

namespace OAI

/-! # Exact subset unions behind the chosen stream occurrences -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def leafMask (x : RepresentationLeaf.Occurrence (Fin n)) : Finset (Fin n) :=
  (x.1.1 ∪ x.1.2) ∪ x.2

def maskFirstChild (z : Layout n) (f : R.Partitions z) (B : Fin n → Fin 2 × Fin 4)
    (D : Fin 3 → Finset (Fin n)) (j : Fin 2) : Finset (Fin n) :=
  leafMask (R.maskLeafOccurrence z f B D j 0) ∪
    leafMask (R.maskLeafOccurrence z f B D j 1)

theorem firstTop_eq_block_union (z : Layout n) (f : R.Partitions z) (D : Finset (Fin n)) :
    R.firstTop z f D = (D ∩ R.rawPartitionBlock z f 0 0) ∪
      (D ∩ R.rawPartitionBlock z f 0 1) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hxD, hxM, hxlt⟩ := Finset.mem_filter.mp hx
    have he : ((f 0).val ⟨x, hxM⟩).val = 0 ∨ ((f 0).val ⟨x, hxM⟩).val = 1 := by omega
    rcases he with he | he
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨hxD, Finset.mem_filter.mpr ⟨hxM, hxM, he⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
        ⟨hxD, Finset.mem_filter.mpr ⟨hxM, hxM, he⟩⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hxD, hxB⟩ := Finset.mem_inter.mp hx
      obtain ⟨_, hxM, he⟩ := Finset.mem_filter.mp hxB
      exact Finset.mem_filter.mpr ⟨hxD, hxM, by omega⟩
    · obtain ⟨hxD, hxB⟩ := Finset.mem_inter.mp hx
      obtain ⟨_, hxM, he⟩ := Finset.mem_filter.mp hxB
      exact Finset.mem_filter.mpr ⟨hxD, hxM, by omega⟩

theorem localBlocks_union (z : Layout n) (f : R.Partitions z) (j : Fin 2) :
    R.rawPartitionBlock z f j.succ 0 ∪ R.rawPartitionBlock z f j.succ 1 =
      R.orderedMixers z j.succ := by
  have hc := R.rawPartitionBlock_biUnion z f j.succ
  fin_cases j
  · change (Finset.univ : Finset (Fin 2)).biUnion
      (fun a => R.rawPartitionBlock z f 1 a.val) = R.orderedMixers z 1 at hc
    change R.rawPartitionBlock z f 1 0 ∪ R.rawPartitionBlock z f 1 1 = R.orderedMixers z 1
    rw [← hc]
    ext x
    simp [Fin.exists_fin_succ]
  · change (Finset.univ : Finset (Fin 2)).biUnion
      (fun a => R.rawPartitionBlock z f 2 a.val) = R.orderedMixers z 2 at hc
    change R.rawPartitionBlock z f 2 0 ∪ R.rawPartitionBlock z f 2 1 = R.orderedMixers z 2
    rw [← hc]
    ext x
    simp [Fin.exists_fin_succ]

theorem localMask_blocks_union (z : Layout n) (f : R.Partitions z) (j : Fin 2)
    (D : Finset (Fin n)) (hD : D ⊆ R.orderedMixers z j.succ) :
    (D ∩ R.rawPartitionBlock z f j.succ 0) ∪
      (D ∩ R.rawPartitionBlock z f j.succ 1) = D := by
  rw [← Finset.inter_union_distrib_left, R.localBlocks_union]
  exact Finset.inter_eq_left.mpr hD

theorem maskFirstChild_parts (z : Layout n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (D : Fin 3 → Finset (Fin n)) (j : Fin 2) :
    R.maskFirstChild z f B D j =
      (R.firstTop z f (orientedMask (j != 0) (D 0) (R.selectedHalves z 0)) ∪
        ((D j.succ ∩ R.rawPartitionBlock z f j.succ 0) ∪
          (D j.succ ∩ R.rawPartitionBlock z f j.succ 1))) ∪
        ((z.2 ∩ R.rawBackground z B j 0) ∪ (z.2 ∩ R.rawBackground z B j 1)) := by
  rw [R.firstTop_eq_block_union]
  simp only [maskFirstChild, leafMask, maskLeafOccurrence, orientedMask]
  norm_num only [Fin.val_zero, Fin.val_one]
  simp only [decide_false, Bool.false_eq_true, ↓reduceIte]
  ac_rfl

theorem maskFirstChild_eq (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (D : Fin 3 → Finset (Fin n)) (hD : ∀ k, D k ⊆ R.selectedHalves z k)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j : Fin 2) :
    R.maskFirstChild z f (R.allocatedBackground z g hn hlog) D j =
      (R.firstTop z f (orientedMask (j != 0) (D 0) (R.selectedHalves z 0)) ∪ D j.succ) ∪
        R.background (R.allocatedChildAssignment hn hlog) z g ⟨2 * j.val, by omega⟩ := by
  let B := R.allocatedBackground z g hn hlog
  have hm := R.localMask_blocks_union z f j (D j.succ)
    ((hD j.succ).trans (R.selectedHalves_subset z j.succ))
  have hb := R.allocated_child_background z g hn hlog j 0
  change R.background (R.allocatedChildAssignment hn hlog) z g ⟨2 * j.val, by omega⟩ =
    (z.2 ∩ R.rawBackground z B j 0) ∪ (z.2 ∩ R.rawBackground z B j 1) at hb
  rw [R.maskFirstChild_parts, hm, ← hb]

theorem chosen_first_children_eq (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) :
    R.maskFirstChild h.1.1.1 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
        (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) 0 =
      R.firstLeftChild (R.allocatedChildAssignment hn hlog) h r ∧
    R.maskFirstChild h.1.1.1 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
        (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) 1 =
      R.firstRightChild (R.allocatedChildAssignment hn hlog) h r := by
  have hD := fun k => (R.chosenMasks_spec _ hr k).1
  constructor
  · rw [R.maskFirstChild_eq _ _ _ _ hD hn hlog 0]
    simp only [firstLeftChild, orientedMask, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    ac_rfl
  · rw [R.maskFirstChild_eq _ _ _ _ hD hn hlog 1]
    simp only [firstRightChild, orientedMask]
    ac_rfl

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
