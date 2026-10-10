import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationChosenMasks

namespace OAI

/-! # Exact weights of the chosen raw representation tuples -/

noncomputable section

namespace LowSpaceSubsetSum

private theorem partition_complement_parts {ι : Type*} [DecidableEq ι]
    (A : Fin 3 → Finset ι) (B : Fin 4 → Finset ι) (D : Finset ι)
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hBA : ∀ i j, Disjoint (B i) (A j))
    (hD : D ⊆ A 0) {S : Finset ι}
    (hcover : ((A 0 ∪ A 1) ∪ A 2) ∪ (((B 0 ∪ B 1) ∪ B 2) ∪ B 3) = S) :
    S \ ((D ∪ A 1) ∪ (B 0 ∪ B 1)) = ((A 0 \ D) ∪ A 2) ∪ (B 2 ∪ B 3) := by
  let L := (D ∪ A 1) ∪ (B 0 ∪ B 1)
  let T := ((A 0 \ D) ∪ A 2) ∪ (B 2 ∪ B 3)
  have hLT : Disjoint L T := by
    dsimp only [L, T]
    simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
    repeat' apply And.intro
    all_goals first
      | exact Finset.disjoint_sdiff
      | exact (hA _ _ (by decide)).mono_left hD
      | exact (hBA _ _).symm.mono_left hD
      | exact (hA _ _ (by decide)).mono_right Finset.sdiff_subset
      | exact hA _ _ (by decide)
      | exact (hBA _ _).symm
      | exact (hBA _ _).mono_right Finset.sdiff_subset
      | exact hBA _ _
      | exact hB _ _ (by decide)
  have hu : L ∪ T = S := by
    calc
      _ = (((D ∪ (A 0 \ D)) ∪ A 1) ∪ A 2) ∪ (((B 0 ∪ B 1) ∪ B 2) ∪ B 3) := by
        dsimp only [L, T]
        ac_rfl
      _ = S := by rw [Finset.union_sdiff_of_subset hD]; exact hcover
  change S \ L = T
  rw [← hu, Finset.union_sdiff_left, Finset.sdiff_eq_self_iff_disjoint.mpr hLT.symm]


namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem topBlocks_union (z : Layout n) (f : R.Partitions z) :
    ((R.rawPartitionBlock z f 0 0 ∪ R.rawPartitionBlock z f 0 1) ∪
      R.rawPartitionBlock z f 0 2) ∪ R.rawPartitionBlock z f 0 3 =
      R.orderedMixers z 0 := by
  have h := R.rawPartitionBlock_biUnion z f 0
  change (Finset.univ : Finset (Fin 4)).biUnion
    (fun a => R.rawPartitionBlock z f 0 a.val) = R.orderedMixers z 0 at h
  rw [← h]
  ext x
  simp [Fin.exists_fin_succ]

theorem maskParent_topMask (z : Layout n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (D : Fin 3 → Finset (Fin n))
    (hD : ∀ k, D k ⊆ R.selectedHalves z k) (j : Fin 2) :
    RepresentationUniverse.topMask (R.maskParentOccurrence z f B D j) =
      orientedMask (j != 0) (D 0) (R.selectedHalves z 0) := by
  have hs : orientedMask (j != 0) (D 0) (R.selectedHalves z 0) ⊆
      R.orderedMixers z 0 := by
    unfold orientedMask
    split_ifs
    · exact Finset.sdiff_subset.trans (R.selectedHalves_subset z 0)
    · exact (hD 0).trans (R.selectedHalves_subset z 0)
  change (((_ ∩ _) ∪ (_ ∩ _)) ∪ (_ ∩ _)) ∪ (_ ∩ _) = _
  rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left,
    ← Finset.inter_union_distrib_left]
  change orientedMask (j != 0) (D 0) (R.selectedHalves z 0) ∩
    (((R.rawPartitionBlock z f 0 0 ∪ R.rawPartitionBlock z f 0 1) ∪
      R.rawPartitionBlock z f 0 2) ∪ R.rawPartitionBlock z f 0 3) = _
  rw [R.topBlocks_union]
  exact Finset.inter_eq_left.mpr hs

theorem maskParent_localMask (z : Layout n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (D : Fin 3 → Finset (Fin n))
    (hD : ∀ k, D k ⊆ R.selectedHalves z k) (j : Fin 2) :
    RepresentationUniverse.localMask (R.maskParentOccurrence z f B D j) =
      R.selectedHalves z j.succ := by
  have hd := R.localMask_blocks_union z f j (D j.succ)
    ((hD j.succ).trans (R.selectedHalves_subset z j.succ))
  have hc := R.localMask_blocks_union z f j (R.selectedHalves z j.succ \ D j.succ)
    (Finset.sdiff_subset.trans (R.selectedHalves_subset z j.succ))
  calc
    _ = ((D j.succ ∩ R.rawPartitionBlock z f j.succ 0) ∪
          (D j.succ ∩ R.rawPartitionBlock z f j.succ 1)) ∪
        (((R.selectedHalves z j.succ \ D j.succ) ∩ R.rawPartitionBlock z f j.succ 0) ∪
          ((R.selectedHalves z j.succ \ D j.succ) ∩ R.rawPartitionBlock z f j.succ 1)) := by
      simp only [RepresentationUniverse.localMask, maskParentOccurrence, maskLeafOccurrence,
        orientedMask]
      norm_num only [Fin.val_zero, Fin.val_one]
      simp only [decide_false, Bool.false_eq_true, ↓reduceIte]
      ac_rfl
    _ = R.selectedHalves z j.succ := by
      rw [hd, hc, Finset.union_sdiff_of_subset (hD j.succ)]

theorem maskParent_backgroundMask (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (D : Fin 3 → Finset (Fin n)) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j : Fin 2) :
    RepresentationUniverse.backgroundMask
        (R.maskParentOccurrence z f (R.allocatedBackground z g hn hlog) D j) =
      R.background (R.allocatedChildAssignment hn hlog) z g ⟨2 * j.val, by omega⟩ ∪
        R.background (R.allocatedChildAssignment hn hlog) z g ⟨2 * j.val + 1, by omega⟩ := by
  have h0 := R.allocated_child_background z g hn hlog j 0
  have h1 := R.allocated_child_background z g hn hlog j 1
  change R.background (R.allocatedChildAssignment hn hlog) z g ⟨2 * j.val, by omega⟩ =
    (z.2 ∩ R.rawBackground z (R.allocatedBackground z g hn hlog) j 0) ∪
      (z.2 ∩ R.rawBackground z (R.allocatedBackground z g hn hlog) j 1) at h0
  change R.background (R.allocatedChildAssignment hn hlog) z g ⟨2 * j.val + 1, by omega⟩ =
    (z.2 ∩ R.rawBackground z (R.allocatedBackground z g hn hlog) j 2) ∪
      (z.2 ∩ R.rawBackground z (R.allocatedBackground z g hn hlog) j 3) at h1
  rw [h0, h1]
  simp only [RepresentationUniverse.backgroundMask, maskParentOccurrence, maskLeafOccurrence]
  ac_rfl

/-- All four assigned pieces partition the solution outside the mixers. -/
theorem background_four_union (B : BackgroundAssignment n) (z : Layout n) (g : Guesses n) :
    ((R.background B z g 0 ∪ R.background B z g 1) ∪ R.background B z g 2) ∪
      R.background B z g 3 = R.outside z := by
  classical
  ext x
  simp only [background, Finset.mem_union, Finset.mem_filter]
  constructor
  · tauto
  · intro hx
    have hc : B z g x = 0 ∨ B z g x = 1 ∨ B z g x = 2 ∨ B z g x = 3 := by
      generalize B z g x = c
      fin_cases c <;> simp
    tauto

theorem solution_halves_outside (z : Layout n) :
    ((R.selectedHalves z 0 ∪ R.selectedHalves z 1) ∪ R.selectedHalves z 2) ∪
      R.outside z = z.2 := by
  change (((z.2 ∩ _) ∪ (z.2 ∩ _)) ∪ (z.2 ∩ _)) ∪ (z.2 \ _) = z.2
  rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left]
  ext x
  simp only [mixerUnion, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- The complementary parent's concrete three pieces equal the named set difference. -/
theorem rightParent_parts (B : BackgroundAssignment n) {h : R.PrimeHistory}
    {r : R.Residues h.2} (hr : R.ResidueSuccess (R.actualOffsets B) h r) :
    R.rightParent B h r =
      ((R.selectedHalves h.1.1.1 0 \ R.chosenMasks (R.actualOffsets B) h r 0) ∪
        R.selectedHalves h.1.1.1 2) ∪
      (R.background B h.1.1.1 h.1.1.2 2 ∪ R.background B h.1.1.1 h.1.1.2 3) := by
  classical
  apply partition_complement_parts
    (fun i => R.selectedHalves h.1.1.1 i)
    (fun i => R.background B h.1.1.1 h.1.1.2 i)
    (R.chosenMasks (R.actualOffsets B) h r 0)
  · exact fun _ _ hij => R.selectedHalves_disjoint _ hij
  · exact fun _ _ hij => R.background_disjoint _ _ _ hij
  · exact fun i j => (R.background_disjoint_mixer B _ _ i j).mono_right
      (R.selectedHalves_subset _ j)
  · exact (R.chosenMasks_spec _ hr 0).1
  · rw [R.background_four_union]
    exact R.solution_halves_outside _


/-- The union of every component of a raw parent. -/
def maskParentSet (z : Layout n) (f : R.Partitions z) (B : Fin n → Fin 2 × Fin 4)
    (D : Fin 3 → Finset (Fin n)) (j : Fin 2) : Finset (Fin n) :=
  let x := R.maskParentOccurrence z f B D j
  (RepresentationUniverse.topMask x ∪ RepresentationUniverse.localMask x) ∪
    RepresentationUniverse.backgroundMask x

theorem maskParentSet_eq (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (D : Fin 3 → Finset (Fin n)) (hD : ∀ k, D k ⊆ R.selectedHalves z k)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j : Fin 2) :
    R.maskParentSet z f (R.allocatedBackground z g hn hlog) D j =
      (orientedMask (j != 0) (D 0) (R.selectedHalves z 0) ∪ R.selectedHalves z j.succ) ∪
      (R.background (R.allocatedChildAssignment hn hlog) z g ⟨2 * j.val, by omega⟩ ∪
        R.background (R.allocatedChildAssignment hn hlog) z g ⟨2 * j.val + 1, by omega⟩) := by
  simp only [maskParentSet, R.maskParent_topMask z f _ D hD,
    R.maskParent_localMask z f _ D hD, R.maskParent_backgroundMask]

theorem chosen_parent_sets_eq (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) :
    R.maskParentSet h.1.1.1 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
        (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) 0 =
      R.leftParent (R.allocatedChildAssignment hn hlog) h r ∧
    R.maskParentSet h.1.1.1 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
        (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) 1 =
      R.rightParent (R.allocatedChildAssignment hn hlog) h r := by
  have hD := fun k => (R.chosenMasks_spec _ hr k).1
  constructor
  · rw [R.maskParentSet_eq _ _ _ _ hD hn hlog 0]
    rfl
  · rw [R.maskParentSet_eq _ _ _ _ hD hn hlog 1,
      R.rightParent_parts _ hr]
    rfl

/-- Different component types live in disjoint mixer/background regions. -/
theorem mask_components_disjoint (z : Layout n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (D : Fin 3 → Finset (Fin n)) (j : Fin 2)
    (i k : Fin 4) :
    Disjoint (R.maskLeafOccurrence z f B D j i).1.1
        (R.maskLeafOccurrence z f B D j k).1.2 ∧
    Disjoint (R.maskLeafOccurrence z f B D j i).1.1
        (R.maskLeafOccurrence z f B D j k).2 ∧
    Disjoint (R.maskLeafOccurrence z f B D j i).1.2
        (R.maskLeafOccurrence z f B D j k).2 := by
  have ht := (Finset.inter_subset_right (s₁ := orientedMask (j != 0) (D 0)
      (R.selectedHalves z 0)) (s₂ := R.rawPartitionBlock z f 0 i.val)).trans
      (R.rawPartitionBlock_subset z f 0 i.val)
  have hl (k : Fin 4) := (Finset.inter_subset_right
      (s₁ := orientedMask (decide (2 ≤ k.val)) (D j.succ) (R.selectedHalves z j.succ))
      (s₂ := R.rawPartitionBlock z f j.succ (k.val % 2))).trans
      (R.rawPartitionBlock_subset z f j.succ (k.val % 2))
  have hb : (R.maskLeafOccurrence z f B D j k).2 ⊆ Finset.univ \ R.mixerUnion z :=
    Finset.inter_subset_right.trans (Finset.filter_subset _ _)
  have hbg (a : Fin 3) : Disjoint (R.orderedMixers z a) (Finset.univ \ R.mixerUnion z) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    apply (Finset.mem_sdiff.mp hy).2
    fin_cases a
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    · exact Finset.mem_union_right _ hx
  exact ⟨(R.orderedMixers_disjoint z (by intro he; have hv := congrArg Fin.val he; simp at hv)).mono ht (hl k),
    (hbg 0).mono ht hb, (hbg j.succ).mono (hl i) hb⟩

theorem maskParentOccurrence_weight (a : Fin n → ℤ) (z : Layout n)
    (f : R.Partitions z) (B : Fin n → Fin 2 × Fin 4)
    (D : Fin 3 → Finset (Fin n)) (j : Fin 2) :
    RepresentationUniverse.parentWeight a (R.maskParentOccurrence z f B D j) =
      weight a (R.maskParentSet z f B D j) := by
  have hd (i k : Fin 4) := R.mask_components_disjoint z f B D j i k
  have htl : Disjoint (RepresentationUniverse.topMask (R.maskParentOccurrence z f B D j))
      (RepresentationUniverse.localMask (R.maskParentOccurrence z f B D j)) := by
    simp only [RepresentationUniverse.topMask, RepresentationUniverse.localMask,
      maskParentOccurrence, Finset.disjoint_union_left, Finset.disjoint_union_right]
    repeat' apply And.intro
    all_goals exact (hd _ _).1
  have htb : Disjoint (RepresentationUniverse.topMask (R.maskParentOccurrence z f B D j))
      (RepresentationUniverse.backgroundMask (R.maskParentOccurrence z f B D j)) := by
    simp only [RepresentationUniverse.topMask, RepresentationUniverse.backgroundMask,
      maskParentOccurrence, Finset.disjoint_union_left, Finset.disjoint_union_right]
    repeat' apply And.intro
    all_goals exact (hd _ _).2.1
  have hlb : Disjoint (RepresentationUniverse.localMask (R.maskParentOccurrence z f B D j))
      (RepresentationUniverse.backgroundMask (R.maskParentOccurrence z f B D j)) := by
    simp only [RepresentationUniverse.localMask, RepresentationUniverse.backgroundMask,
      maskParentOccurrence, Finset.disjoint_union_left, Finset.disjoint_union_right]
    repeat' apply And.intro
    all_goals exact (hd _ _).2.2
  rw [RepresentationUniverse.valid_weight a (R.maskParentOccurrence_valid z f B D j),
    maskParentSet, weight_union a (Finset.disjoint_union_left.mpr ⟨htb, hlb⟩),
    weight_union a htl]


theorem maskFirstChild_weight (a : Fin n → ℤ) (z : Layout n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (D : Fin 3 → Finset (Fin n)) (j : Fin 2) :
    RepresentationUniverse.childWeight a (R.maskParentOccurrence z f B D j).1 =
      weight a (R.maskFirstChild z f B D j) := by
  let x := R.maskLeafOccurrence z f B D j 0
  let y := R.maskLeafOccurrence z f B D j 1
  have hv := R.maskParentOccurrence_valid z f B D j
  have hd (i k : Fin 4) := R.mask_components_disjoint z f B D j i k
  have htl : Disjoint (x.1.1 ∪ y.1.1) (x.1.2 ∪ y.1.2) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨(hd 0 0).1, (hd 0 1).1⟩,
        Finset.disjoint_union_right.mpr ⟨(hd 1 0).1, (hd 1 1).1⟩⟩
  have htb : Disjoint (x.1.1 ∪ y.1.1) (x.2 ∪ y.2) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨(hd 0 0).2.1, (hd 0 1).2.1⟩,
        Finset.disjoint_union_right.mpr ⟨(hd 1 0).2.1, (hd 1 1).2.1⟩⟩
  have hlb : Disjoint (x.1.2 ∪ y.1.2) (x.2 ∪ y.2) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨(hd 0 0).2.2, (hd 0 1).2.2⟩,
        Finset.disjoint_union_right.mpr ⟨(hd 1 0).2.2, (hd 1 1).2.2⟩⟩
  have he : R.maskFirstChild z f B D j = ((x.1.1 ∪ y.1.1) ∪
      (x.1.2 ∪ y.1.2)) ∪ (x.2 ∪ y.2) := by
    dsimp only [maskFirstChild, leafMask, x, y]
    ac_rfl
  have hxt : Disjoint x.1.1 y.1.1 := hv.1.1
  have hxl : Disjoint x.1.2 y.1.2 := hv.2.1.1
  have hxb : Disjoint x.2 y.2 := hv.2.2.1
  rw [he, weight_union a (Finset.disjoint_union_left.mpr ⟨htb, hlb⟩),
    weight_union a htl, weight_union a hxt, weight_union a hxl, weight_union a hxb]
  simp only [RepresentationUniverse.childWeight, RepresentationLeaf.occurrenceWeight,
    maskParentOccurrence, x, y]
  ring

/-- All six raw tuple weights are the weights used by the survival event. -/
theorem chosen_raw_weights (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) :
    let B := R.allocatedChildAssignment hn hlog
    let P := R.maskParentOccurrence h.1.1.1 h.1.2
      (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
      (R.chosenMasks (R.actualOffsets B) h r)
    let a := R.signedWeights h.1.1.1
    RepresentationUniverse.parentWeight a (P 0) = weight a (R.leftParent B h r) ∧
    RepresentationUniverse.parentWeight a (P 1) = weight a (R.rightParent B h r) ∧
    RepresentationUniverse.childWeight a (P 0).1 = weight a (R.firstLeftChild B h r) ∧
    RepresentationUniverse.childWeight a (P 0).2 = weight a (R.secondLeftChild B h r) ∧
    RepresentationUniverse.childWeight a (P 1).1 = weight a (R.firstRightChild B h r) ∧
    RepresentationUniverse.childWeight a (P 1).2 = weight a (R.secondRightChild B h r) := by
  dsimp only
  have hp := R.chosen_parent_sets_eq h r hn hlog hr
  have hc := R.chosen_first_children_eq h r hn hlog hr
  have hp0 := R.maskParentOccurrence_weight (R.signedWeights h.1.1.1) h.1.1.1 h.1.2
    (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
    (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) 0
  have hp1 := R.maskParentOccurrence_weight (R.signedWeights h.1.1.1) h.1.1.1 h.1.2
    (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
    (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) 1
  have hc0 := R.maskFirstChild_weight (R.signedWeights h.1.1.1) h.1.1.1 h.1.2
    (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
    (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) 0
  have hc1 := R.maskFirstChild_weight (R.signedWeights h.1.1.1) h.1.1.1 h.1.2
    (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
    (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) 1
  rw [hp.1] at hp0
  rw [hp.2] at hp1
  rw [hc.1] at hc0
  rw [hc.2] at hc1
  refine ⟨hp0, hp1, hc0, ?_, hc1, ?_⟩
  · rw [secondLeftChild, weight_complement _ (R.firstLeftChild_subset_parent _ hr)]
    dsimp only [RepresentationUniverse.parentWeight] at hp0
    omega
  · rw [secondRightChild, weight_complement _ (R.firstRightChild_subset_parent _ hr)]
    dsimp only [RepresentationUniverse.parentWeight] at hp1
    omega

/-- The six congruences hold for the actual raw tuples fed to the pair streams. -/
theorem chosen_raw_filters (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) :
    let B := R.allocatedChildAssignment hn hlog
    let P := R.maskParentOccurrence h.1.1.1 h.1.2
      (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
      (R.chosenMasks (R.actualOffsets B) h r)
    let a := R.signedWeights h.1.1.1
    let p := prefixModulus h.2.val
    RepresentationUniverse.parentWeight a (P 0) ≡ (r.1.val : ℤ) [ZMOD (p 0 : ℤ)] ∧
    RepresentationUniverse.parentWeight a (P 1) ≡
      R.signedTarget h.1.1.1 - (r.1.val : ℤ) [ZMOD (p 0 : ℤ)] ∧
    RepresentationUniverse.childWeight a (P 0).1 ≡ (r.2.1.val : ℤ) [ZMOD (p 1 : ℤ)] ∧
    RepresentationUniverse.childWeight a (P 0).2 ≡
      (r.1.val : ℤ) - r.2.1.val [ZMOD (p 1 : ℤ)] ∧
    RepresentationUniverse.childWeight a (P 1).1 ≡ (r.2.2.val : ℤ) [ZMOD (p 2 : ℤ)] ∧
    RepresentationUniverse.childWeight a (P 1).2 ≡
      (R.signedTarget h.1.1.1 - (r.1.val : ℤ)) - r.2.2.val [ZMOD (p 2 : ℤ)] := by
  dsimp only
  obtain ⟨hp0, hp1, hc0, hc0', hc1, hc1'⟩ := R.chosen_raw_weights h r hn hlog hr
  rw [hp0, hp1, hc0, hc0', hc1, hc1']
  exact R.actualFilters_of_hits (R.allocatedChildAssignment hn hlog) hr


end RepresentationSetup

end LowSpaceSubsetSum

end

end OAI
