import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationChosenWeights
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationParentComplete

namespace OAI

/-! # The surviving representation in the executable parent streams -/

noncomputable section

namespace LowSpaceSubsetSum

namespace MaskRestriction

/-- Restricting a compatible full mask to a leaf preserves its prefix tests. -/
theorem compatible_inter {n : ℕ} (P : MaskRestriction n)
    {M S A : Finset (Fin n)} (hA : A ⊆ M) (h : P.Compatible M S) :
    P.Compatible A (S ∩ A) := by
  constructor
  · intro i hi
    obtain ⟨hiP, hiA⟩ := Finset.mem_inter.mp hi
    exact Finset.mem_inter.mpr ⟨h.1 (Finset.mem_inter.mpr ⟨hiP, hA hiA⟩), hiA⟩
  · exact h.2.mono_right Finset.inter_subset_left

end MaskRestriction

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def chosenRawParent (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (j : Fin 2) : RepresentationUniverse.ParentOccurrence (Fin n) :=
  R.maskParentOccurrence h.1.1.1 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
    (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) j

def chosenNamedParent (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (j : Fin 2) : Finset (Fin n) :=
  if j = 0 then R.leftParent (R.allocatedChildAssignment hn hlog) h r
  else R.rightParent (R.allocatedChildAssignment hn hlog) h r

/-- The designated analysis task uses one of the actual normalized parent
residues. The program itself receives only the primitive data of this record. -/
def chosenParentData (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (j : Fin 2) (P : ℤ) (hP : 0 < P) (C : ℕ) (restriction : MaskRestriction n) :
    RepresentationParentData n where
  input := R.input
  signs := R.signMask h.1.1.1
  leaves := R.rawLeaf h.1.1.1 h.1.1.2 h.1.2
    (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) j
  lowModulus := prefixModulus h.2.val j.succ
  modulus := P
  positive := hP
  childResidues k :=
    let first : ℤ := if j = 0 then r.2.1.val else r.2.2.val
    let parent : ℤ := if j = 0 then r.1.val else R.signedTarget h.1.1.1 - r.1.val
    if k = 0 then first else parent - first
  parentResidue := weight (R.signedWeights h.1.1.1) (R.chosenNamedParent h r hn hlog j) % P
  capacity := C
  maskRestriction := restriction

@[simp] theorem chosenParentData_weights (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (j : Fin 2) (P : ℤ) (hP : 0 < P) (C : ℕ) (restriction : MaskRestriction n) :
    (R.chosenParentData h r hn hlog j P hP C restriction).weights =
      R.signedWeights h.1.1.1 := rfl

theorem chosenRawParent_weight (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (j : Fin 2) :
    RepresentationUniverse.parentWeight (R.signedWeights h.1.1.1)
      (R.chosenRawParent h r hn hlog j) =
      weight (R.signedWeights h.1.1.1) (R.chosenNamedParent h r hn hlog j) := by
  have hw := R.chosen_raw_weights h r hn hlog hr
  fin_cases j
  · exact hw.1
  · exact hw.2.1

theorem chosenRawParent_topMask (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (j : Fin 2) :
    RepresentationUniverse.topMask (R.chosenRawParent h r hn hlog j) =
      orientedMask (j != 0) (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r 0)
        (R.selectedHalves h.1.1.1 0) :=
  R.maskParent_topMask _ _ _ _ (fun k => (R.chosenMasks_spec _ hr k).1) j

theorem chosenLeaf_compatible (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (j : Fin 2) (restriction : MaskRestriction n)
    (hcompat : restriction.Compatible (R.orderedMixers h.1.1.1 0)
      (orientedMask (j != 0)
        (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r 0)
        (R.selectedHalves h.1.1.1 0))) (i : Fin 4) :
    restriction.Compatible
      (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2
        (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) j i).top
      (R.maskLeafOccurrence h.1.1.1 h.1.2
        (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
        (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) j i).1.1 :=
  restriction.compatible_inter (R.rawPartitionBlock_subset _ _ _ _) hcompat

/-- Both low-filtered children, their high-key match, and exact local validity
hold for the same chosen raw parent. No array-membership premise is assumed. -/
theorem chosenRawParent_eligible (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (j : Fin 2) (P : ℤ) (hP : 0 < P) (C : ℕ) (restriction : MaskRestriction n)
    (hcompat : restriction.Compatible (R.orderedMixers h.1.1.1 0)
      (orientedMask (j != 0)
        (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r 0)
        (R.selectedHalves h.1.1.1 0))) :
    (R.chosenParentData h r hn hlog j P hP C restriction).RawEligible
      (R.chosenRawParent h r hn hlog j) := by
  let D := R.chosenParentData h r hn hlog j P hP C restriction
  have hf := R.chosen_raw_filters h r hn hlog hr
  have hleaf := R.chosenLeaf_compatible h r hn hlog j restriction hcompat
  apply D.rawEligible_of_filters
  · exact R.chosenParentOccurrence_mem (R.allocatedChildAssignment hn hlog) h r hr _ j
  · exact R.maskParentOccurrence_valid _ _ _ _ j
  · exact hleaf 0
  · exact hleaf 1
  · exact hleaf 2
  · exact hleaf 3
  · fin_cases j
    · exact hf.2.2.1
    · exact hf.2.2.2.2.1
  · fin_cases j
    · exact hf.2.2.2.1
    · exact hf.2.2.2.2.2
  · change RepresentationUniverse.parentWeight (R.signedWeights h.1.1.1)
      (R.chosenRawParent h r hn hlog j) % P = _
    rw [R.chosenRawParent_weight h r hn hlog hr j]
    exact (Int.emod_emod _ _).symm

/-- The emitted entry is the exact chosen weight/top-mask key. -/
theorem chosenEntry_rawEntries (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (j : Fin 2) (P : ℤ) (hP : 0 < P) (C : ℕ) (restriction : MaskRestriction n)
    (hcompat : restriction.Compatible (R.orderedMixers h.1.1.1 0)
      (orientedMask (j != 0)
        (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r 0)
        (R.selectedHalves h.1.1.1 0))) :
    RepresentationUniverse.entry (R.signedWeights h.1.1.1) (R.chosenRawParent h r hn hlog j) ∈
      (R.chosenParentData h r hn hlog j P hP C restriction).rawEntries := by
  exact ((R.chosenParentData h r hn hlog j P hP C restriction).rawEntries_mem _).mpr
    ⟨R.chosenRawParent h r hn hlog j,
      R.chosenRawParent_eligible h r hn hlog hr j P hP C restriction hcompat, rfl⟩

/-- The two concrete entry keys still partition the chosen top half and
sum to the signed target after raw tuple generation. -/
theorem chosenEntries_match (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) :
    let e := fun j => RepresentationUniverse.entry (R.signedWeights h.1.1.1)
      (R.chosenRawParent h r hn hlog j)
    (e 0).value + (e 1).value = R.signedTarget h.1.1.1 ∧
    Disjoint (e 0).mask (e 1).mask ∧
    (e 0).mask ∪ (e 1).mask = R.selectedHalves h.1.1.1 0 := by
  dsimp only
  have hw := R.chosen_raw_weights h r hn hlog hr
  have ht0 := R.chosenRawParent_topMask h r hn hlog hr 0
  have ht1 := R.chosenRawParent_topMask h r hn hlog hr 1
  change RepresentationUniverse.topMask (R.chosenRawParent h r hn hlog 0) =
    R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r 0 at ht0
  change RepresentationUniverse.topMask (R.chosenRawParent h r hn hlog 1) =
    R.selectedHalves h.1.1.1 0 \ R.chosenMasks
      (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r 0 at ht1
  refine ⟨?_, ?_, ?_⟩
  · change RepresentationUniverse.parentWeight (R.signedWeights h.1.1.1) _ +
      RepresentationUniverse.parentWeight (R.signedWeights h.1.1.1) _ = _
    dsimp only [chosenRawParent]
    rw [hw.1, hw.2.1, R.leftParent_weight _ hr, R.rightParent_weight _ hr]
    ring
  · change Disjoint (RepresentationUniverse.topMask _) (RepresentationUniverse.topMask _)
    rw [ht0, ht1]
    exact Finset.disjoint_sdiff
  · change RepresentationUniverse.topMask _ ∪ RepresentationUniverse.topMask _ = _
    rw [ht0, ht1]
    exact Finset.union_sdiff_of_subset (R.chosenMasks_spec _ hr 0).1


theorem mixer_disjoint_rawOutside (z : Layout n) (i : Fin 3) :
    Disjoint (R.orderedMixers z i) (Finset.univ \ R.mixerUnion z) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  apply (Finset.mem_sdiff.mp hy).2
  fin_cases i
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  · exact Finset.mem_union_right _ hx

theorem rawLeaf_domains_disjoint (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) :
    Disjoint (RepresentationUniverse.topDomain (R.rawLeaf z g f B j))
        (RepresentationUniverse.mixerDomain (R.rawLeaf z g f B j)) ∧
    Disjoint (RepresentationUniverse.topDomain (R.rawLeaf z g f B j))
        (RepresentationUniverse.backgroundDomain (R.rawLeaf z g f B j)) ∧
    Disjoint (RepresentationUniverse.mixerDomain (R.rawLeaf z g f B j))
        (RepresentationUniverse.backgroundDomain (R.rawLeaf z g f B j)) := by
  have hb : RepresentationUniverse.backgroundDomain (R.rawLeaf z g f B j) ⊆
      Finset.univ \ R.mixerUnion z := by
    change ((R.rawBackground z B j 0 ∪ R.rawBackground z B j 1) ∪
      R.rawBackground z B j 2) ∪ R.rawBackground z B j 3 ⊆ _
    repeat' apply Finset.union_subset
    all_goals exact Finset.filter_subset _ _
  rw [R.rawLeaf_topDomain, R.rawLeaf_mixerDomain]
  exact ⟨R.orderedMixers_disjoint z (by intro he; have hv := congrArg Fin.val he; simp at hv),
    (R.mixer_disjoint_rawOutside z 0).mono_right hb,
    (R.mixer_disjoint_rawOutside z j.succ).mono_right hb⟩

theorem raw_validEntries_bounded (z : Layout n) (g : Guesses n) (f : R.Partitions z)
    (B : Fin n → Fin 2 × Fin 4) (j : Fin 2) (e : Entry (Fin n))
    (he : e ∈ RepresentationUniverse.validEntries (R.signedWeights z) (R.rawLeaf z g f B j)) :
    WeightEncoding.BoundedWeight R.input e.value := by
  classical
  let : DecidablePred (RepresentationUniverse.Valid (ι := Fin n)) :=
    fun _ => Classical.propDecidable _
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hx, hv⟩ := Finset.mem_filter.mp hx
  have hd := R.rawLeaf_domains_disjoint z g f B j
  obtain ⟨S, _, hw, _⟩ := RepresentationUniverse.entry_represents (R.signedWeights z)
    (R.rawLeaf z g f B j) hd.1 hd.2.1 hd.2.2 hx hv
  rw [← hw]
  exact WeightEncoding.signed_weight_bounded R.input (R.signMask z) S

/-- The actual distinct-entry bucket containing the designated representation. -/
def chosenParentBucket (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (j : Fin 2) (P : ℤ) : Finset (Entry (Fin n)) :=
  (RepresentationUniverse.validEntries (R.signedWeights h.1.1.1)
    (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2
      (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) j)).filter
        (fun e => e.value % P = weight (R.signedWeights h.1.1.1)
          (R.chosenNamedParent h r hn hlog j) % P)

theorem chosenParent_rawEntries_subset (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (j : Fin 2) (P : ℤ) (hP : 0 < P) (C : ℕ) (restriction : MaskRestriction n)
    (e : Entry (Fin n))
    (he : e ∈ (R.chosenParentData h r hn hlog j P hP C restriction).rawEntries) :
    e ∈ R.chosenParentBucket h r hn hlog j P := by
  classical
  let : DecidablePred (RepresentationUniverse.Valid (ι := Fin n)) :=
    fun _ => Classical.propDecidable _
  let D := R.chosenParentData h r hn hlog j P hP C restriction
  have hp := D.rawEntries_parent_mod e he
  have hx := (D.rawEntries_mem e).mp he
  obtain ⟨x, ⟨hx, hy, _, hv⟩, rfl⟩ := hx
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
      ⟨D.streams_parent x.1 x.2 hx hy, hv⟩, rfl⟩
  · simpa only [D, chosenParentData, Int.emod_emod] using hp

/-- Capacity is measured on distinct exact entries. Once this actual bucket
fits, every compatible chosen witness reaches the bounded array. -/
theorem chosenEntry_collected (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (j : Fin 2) (P : ℤ) (hP : 0 < P) (C B : ℕ) (restriction : MaskRestriction n)
    (hcompat : restriction.Compatible (R.orderedMixers h.1.1.1 0)
      (orientedMask (j != 0)
        (R.chosenMasks (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r 0)
        (R.selectedHalves h.1.1.1 0)))
    (hcap : (R.chosenParentBucket h r hn hlog j P).card ≤ C) :
    ((R.chosenParentData h r hn hlog j P hP C restriction).collect B).state.user.keys.overflow = false ∧
    RepresentationUniverse.entry (R.signedWeights h.1.1.1) (R.chosenRawParent h r hn hlog j) ∈
      ((R.chosenParentData h r hn hlog j P hP C restriction).entries B).toList := by
  let D := R.chosenParentData h r hn hlog j P hP C restriction
  let U := R.chosenParentBucket h r hn hlog j P
  have hU : ∀ e ∈ D.rawEntries, e ∈ U :=
    R.chosenParent_rawEntries_subset h r hn hlog j P hP C restriction
  have hb : ∀ e ∈ U, WeightEncoding.BoundedWeight D.input e.value := by
    intro e he
    exact R.raw_validEntries_bounded _ _ _ _ j e (Finset.mem_filter.mp he).1
  refine ⟨(D.collect_fits B U hcap hU).1, ?_⟩
  apply (D.entries_mem_iff B U hcap hU hb _).mpr
  exact R.chosenEntry_rawEntries h r hn hlog hr j P hP C restriction hcompat

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
