import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleWitness
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PrefixTaskCount
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CheckListWork

namespace OAI

/-! # Prefix work for the actual representation schedule

The bounds apply to every lifted residue and every prefix, without requiring
a surviving solution. The check list is fixed before separator families are
drawn, including all reuse of the retained left array.
-/

noncomputable section

namespace LowSpaceSubsetSum

namespace RepresentationBucketData

variable {n g : ℕ} (D : RepresentationBucketData n g)

theorem checkInputSize_le (B : ℕ) (hcapacity : D.left.capacity = D.right.capacity)
    (hleftBounded : ∀ e ∈ D.left.rawEntries, WeightEncoding.BoundedWeight D.left.input e.value)
    (hd : ∀ i j, i ≠ j → Disjoint (D.right.leaves i).top (D.right.leaves j).top)
    (hbounded : ∀ P, ∀ e ∈ ({ D.right with maskRestriction := P }).rawEntries,
      WeightEncoding.BoundedWeight D.right.input e.value)
    (horder : ∀ i ∈ D.topOrder, i ∈ RepresentationUniverse.topDomain D.right.leaves) :
    TopCoordinates.checkInputSize (D.checkList B) ≤ D.left.entryUniverse.card +
      (2 * D.topOrder.length + 3) *
        ({ D.right with maskRestriction := MaskRestriction.empty }).entryUniverse.card := by
  unfold checkList
  dsimp only
  split
  · simp [TopCoordinates.checkInputSize]
  · rename_i hclear
    have hclear' := Bool.eq_false_iff.mpr hclear
    split
    · simp [TopCoordinates.checkInputSize]
    · have hsize := D.left.completed_size_le B hclear'
      have hsize' : (D.left.entries B).size ≤ D.right.capacity := hcapacity ▸ hsize
      have hb := D.right.completed_check_inputs_le B (D.left.entries B).size hsize'
        hd hbounded D.topOrder horder MaskRestriction.empty
      simp only [TopCoordinates.checkInputSize, List.map_map]
      change ((D.right.completedArrays B D.topOrder MaskRestriction.empty).map
        (fun a => (D.left.entries B).size + a.size)).sum ≤ _
      have he := D.left.completed_size_eq_card B hleftBounded hclear'
      generalize hL : D.left.entries B = left at hb he ⊢
      rw [he] at hb ⊢
      exact hb

theorem checkList_arrays (B : ℕ) (p : TopCoordinates.CheckInputs n)
    (hp : p ∈ D.checkList B) :
    p.1 = D.left.entries B ∧ ∃ P : MaskRestriction n,
      p.2 = ({ D.right with maskRestriction := P }).entries B := by
  unfold checkList at hp
  dsimp only at hp
  split at hp
  · simp at hp
  · split at hp
    · simp at hp
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      obtain ⟨P, _, he⟩ := D.right.mem_completedArrays B D.topOrder MaskRestriction.empty a ha
      exact ⟨rfl, P, he⟩

end RepresentationBucketData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)
variable (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
variable (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
variable (q : ℕ) (hq : 0 < q)

/-- The four actual top blocks are disjoint at every task. -/
theorem schedule_top_disjoint (z : ℕ) (side : Fin 2) :
    ∀ i j, i ≠ j →
      Disjoint (((R.scheduleData h r hn hlog q hq).parentData side z).leaves i).top
        (((R.scheduleData h r hn hlog q hq).parentData side z).leaves j).top := by
  intro i j hij
  exact R.rawPartitionBlock_disjoint h.1.1.1 h.1.2 0 (fun he => hij (Fin.ext he))

theorem schedule_topOrder_length :
    (R.scheduleData h r hn hlog q hq).topOrder.length = mixerSize n := by
  change ((R.orderedMixers h.1.1.1 0).sort (· ≤ ·)).length = _
  rw [Finset.length_sort, R.orderedMixers_card_mixerSize]

theorem schedule_topOrder_mem (z : ℕ) (side : Fin 2) :
    ∀ i ∈ (R.scheduleData h r hn hlog q hq).topOrder,
      i ∈ RepresentationUniverse.topDomain
        ((R.scheduleData h r hn hlog q hq).parentData side z).leaves := by
  intro i hi
  change i ∈ (R.orderedMixers h.1.1.1 0).sort (· ≤ ·) at hi
  change i ∈ RepresentationUniverse.topDomain
    (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2
      (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) side)
  rw [R.rawLeaf_topDomain]
  exact (Finset.mem_sort (· ≤ ·)).mp hi

/-- Any emitted entry comes from the actual valid four-leaf universe. -/
theorem schedule_rawEntries_valid (z : ℕ) (side : Fin 2) (P : MaskRestriction n)
    (e : Entry (Fin n))
    (he : e ∈ ({ (R.scheduleData h r hn hlog q hq).parentData side z with
      maskRestriction := P }).rawEntries) :
    e ∈ RepresentationUniverse.validEntries (R.signedWeights h.1.1.1)
      (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2
        (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) side) := by
  classical
  let : DecidableEq (Entry (Fin n)) := fun _ _ => Classical.propDecidable _
  let : DecidablePred (RepresentationUniverse.Valid (ι := Fin n)) :=
    fun _ => Classical.propDecidable _
  let D := { (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }
  obtain ⟨x, ⟨hx, hy, _, hv⟩, rfl⟩ := (D.rawEntries_mem e).mp he
  exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
    ⟨D.streams_parent x.1 x.2 hx hy, hv⟩, rfl⟩

/-- Fixed-width keys are injective on every actual prefix's emitted entries. -/
theorem schedule_rawEntries_bounded (z : ℕ) (side : Fin 2) (P : MaskRestriction n)
    (e : Entry (Fin n))
    (he : e ∈ ({ (R.scheduleData h r hn hlog q hq).parentData side z with
      maskRestriction := P }).rawEntries) :
    WeightEncoding.BoundedWeight R.input e.value :=
  R.raw_validEntries_bounded _ _ _ _ side e
    (R.schedule_rawEntries_valid h r hn hlog q hq z side P e he)

/-- Every actual prefix task is charged to the distinct unrestricted bucket. -/
theorem schedule_taskStarts_bound (z : ℕ) (B : ℕ) (side : Fin 2) :
    compressionDictionaryCapacity n *
      ((R.scheduleData h r hn hlog q hq).parentData side z).taskStarts B
        (R.scheduleData h r hn hlog q hq).topOrder MaskRestriction.empty ≤
      compressionDictionaryCapacity n + 2 * (mixerSize n + 1) *
        ((R.scheduleData h r hn hlog q hq).parentData side z).entryUniverse.card := by
  let D := (R.scheduleData h r hn hlog q hq).parentData side z
  have ht := D.taskStarts_capacity B (R.schedule_top_disjoint h r hn hlog q hq z side)
    (R.schedule_rawEntries_bounded h r hn hlog q hq z side)
    (R.scheduleData h r hn hlog q hq).topOrder
    (R.schedule_topOrder_mem h r hn hlog q hq z side) MaskRestriction.empty
  have he : { D with maskRestriction := MaskRestriction.empty } = D := rfl
  rw [he, R.schedule_topOrder_length h r hn hlog q hq] at ht
  exact ht

/-- The concrete check list accounts for the left array each time it is reused. -/
theorem schedule_checkInputSize_bound (z B : ℕ) :
    TopCoordinates.checkInputSize (((R.scheduleData h r hn hlog q hq).bucket z).checkList B) ≤
      ((R.scheduleData h r hn hlog q hq).parentData 0 z).entryUniverse.card +
        (2 * mixerSize n + 3) *
          ((R.scheduleData h r hn hlog q hq).parentData 1 z).entryUniverse.card := by
  have ht := ((R.scheduleData h r hn hlog q hq).bucket z).checkInputSize_le B rfl
    (R.schedule_rawEntries_bounded h r hn hlog q hq z 0 MaskRestriction.empty)
    (R.schedule_top_disjoint h r hn hlog q hq z 1)
    (R.schedule_rawEntries_bounded h r hn hlog q hq z 1)
    (R.schedule_topOrder_mem h r hn hlog q hq z 1)
  change TopCoordinates.checkInputSize _ ≤
    ((R.scheduleData h r hn hlog q hq).parentData 0 z).entryUniverse.card +
    (2 * (R.scheduleData h r hn hlog q hq).topOrder.length + 3) * _ at ht
  rwa [R.schedule_topOrder_length h r hn hlog q hq] at ht

/-- All actual completed checks have the local counts required by the
rounded separator parameters, regardless of the visited prefix. -/
theorem schedule_checkList_counts (z B : ℕ) :
    ∀ p ∈ ((R.scheduleData h r hn hlog q hq).bucket z).checkList B,
      (∀ x ∈ p.1.toList, ∀ i,
        (SeparatorCheck.localMask i
          ((R.topCoordinates h.1.1.1 h.1.2).encodeEntry x).mask).card =
            (separatorParameters h.1.1.2 (by omega)).c i) ∧
      (∀ x ∈ p.2.toList, ∀ i,
        (SeparatorCheck.localMask i
          ((R.topCoordinates h.1.1.1 h.1.2).encodeEntry x).mask).card =
            (2 * blockHalf n 0) / 2 - (separatorParameters h.1.1.2 (by omega)).c i) := by
  intro p hp
  obtain ⟨hleft, P, hright⟩ :=
    ((R.scheduleData h r hn hlog q hq).bucket z).checkList_arrays B p hp
  constructor
  · intro x hx i
    rw [hleft] at hx
    simpa only [ite_true] using
      R.collected_separator_count _ _ _ _ 0 (by omega) _ rfl B x hx i
  · intro x hx i
    rw [hright] at hx
    simpa only [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] using
      R.collected_separator_count _ _ _ _ 1 (by omega) _ rfl B x hx i

theorem schedule_mean_totalScans (z B u : ℕ) (hu : 256 ≤ u) (hnu : n ≤ u)
    (hgu : 2 * blockHalf n 0 + 1 ≤ u) :
    let S := separatorParameters h.1.1.2 (by omega)
    let checks := ((R.scheduleData h r hn hlog q hq).bucket z).checkList B
    RepresentationMoments.mean (fun draws : SeparatorExpectation.IndependentFamilies
      (2 * blockHalf n 0) S.e S.counts =>
      ((R.topCoordinates h.1.1.1 h.1.2).totalScans
        (SeparatorExpectation.familyArrays draws) (R.signedTarget h.1.1.1) checks : ℝ)) ≤
      (TopCoordinates.checkInputSize checks : ℝ) * (u : ℝ) ^ 22 *
        (2 : ℝ) ^ (((4 * (2 * blockHalf n 0) : ℕ) : ℝ) *
          (1 - binaryEntropy (1 / 4))) := by
  dsimp only
  apply (R.topCoordinates h.1.1.1 h.1.2).mean_totalScans
    (separatorParameters h.1.1.2 (by omega)) u hu hnu hgu
  · intro p hp
    exact (R.schedule_checkList_counts h r hn hlog q hq z B p hp).1
  · intro p hp
    exact (R.schedule_checkList_counts h r hn hlog q hq z B p hp).2

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
