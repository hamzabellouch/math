import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPrefixWork

namespace OAI

/-! # Distinct-entry accounting over the lifted residue loop

Every prefix bucket lies in the actual low-residue entry universe. Different
loop counters have disjoint full-residue buckets, so their total distinct
entry count is bounded by one low-residue universe, without a factor `q`.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace RepresentationScheduleData

variable {n g : ℕ} (D : RepresentationScheduleData n g)

def lowEntryUniverse (side : Fin 2) : Finset (Entry (Fin n)) :=
  (RepresentationUniverse.validEntries
    (flip (fun i => (D.input.values i : ℤ)) D.signs) (D.leaves side)).filter
      (fun e => e.value % (D.p0 : ℤ) =
        (if side = 0 then (D.rho0.val : ℤ) else D.target - D.rho0.val) % (D.p0 : ℤ))

theorem leftResidue_low (z : ℕ) :
    D.leftResidue z % (D.p0 : ℤ) = (D.rho0.val : ℤ) % (D.p0 : ℤ) := by
  simp [leftResidue, Int.add_emod]

theorem parentResidue_low (side : Fin 2) (z : ℕ) :
    (D.parentData side z).parentResidue % (D.p0 : ℤ) =
      (if side = 0 then (D.rho0.val : ℤ) else D.target - D.rho0.val) % (D.p0 : ℤ) := by
  have hd : (D.p0 : ℤ) ∣ D.modulus := dvd_mul_right _ _
  change (if side = 0 then D.leftResidue z else
    (D.target - D.leftResidue z) % D.modulus) % _ = _
  split_ifs
  · exact D.leftResidue_low z
  · rw [Int.emod_emod_of_dvd _ hd, Int.sub_emod, D.leftResidue_low, ← Int.sub_emod]

/-- The actual raw emitted key is in the low-residue envelope, including
when its task has a nonempty prefix restriction. -/
theorem entryUniverse_subset_low (side : Fin 2) (z : ℕ) (P : MaskRestriction n) :
    ({ D.parentData side z with maskRestriction := P }).entryUniverse ⊆
      D.lowEntryUniverse side := by
  classical
  let : DecidableEq (Entry (Fin n)) := fun _ _ => Classical.propDecidable _
  let : DecidablePred (RepresentationUniverse.Valid (ι := Fin n)) :=
    fun _ => Classical.propDecidable _
  intro e he
  have he' : e ∈ ({ D.parentData side z with maskRestriction := P }).rawEntries :=
    List.mem_toFinset.mp he
  let E := { D.parentData side z with maskRestriction := P }
  have hmod := E.rawEntries_parent_mod e he'
  have hd : (D.p0 : ℤ) ∣ D.modulus := dvd_mul_right _ _
  have hlow := congrArg (fun w : ℤ => w % (D.p0 : ℤ)) hmod
  change (e.value % D.modulus) % (D.p0 : ℤ) =
    ((D.parentData side z).parentResidue % D.modulus) % (D.p0 : ℤ) at hlow
  rw [Int.emod_emod_of_dvd _ hd, Int.emod_emod_of_dvd _ hd,
    D.parentResidue_low side z] at hlow
  obtain ⟨x, ⟨hx, hy, _, hv⟩, heq⟩ := (E.rawEntries_mem e).mp he'
  apply Finset.mem_filter.mpr
  refine ⟨?_, hlow⟩
  apply Finset.mem_image.mpr
  exact ⟨x, Finset.mem_filter.mpr ⟨E.streams_parent x.1 x.2 hx hy, hv⟩, heq⟩

theorem leftResidue_range (z : Fin D.q) :
    0 ≤ D.leftResidue z.val ∧ D.leftResidue z.val < D.modulus := by
  have hp : (0 : ℤ) < D.p0 := by exact_mod_cast D.p0_positive
  have hr0 : (0 : ℤ) ≤ D.rho0.val := by positivity
  have hr1 : (D.rho0.val : ℤ) < D.p0 := by exact_mod_cast D.rho0.isLt
  have hz0 : (0 : ℤ) ≤ z.val := by positivity
  have hz1 : (z.val : ℤ) + 1 ≤ D.q := by
    exact_mod_cast (Nat.succ_le_iff.mpr z.isLt)
  dsimp only [leftResidue, modulus]
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hz1 hp.le]

/-- Distinct counters specify distinct parent residues on either side. -/
theorem parentResidue_injective (side : Fin 2) :
    Function.Injective (fun z : Fin D.q =>
      (D.parentData side z.val).parentResidue % D.modulus) := by
  intro z w he
  have hz := D.leftResidue_range z
  have hw := D.leftResidue_range w
  have hleft : D.leftResidue z.val = D.leftResidue w.val := by
    fin_cases side
    · change D.leftResidue z.val % D.modulus = D.leftResidue w.val % D.modulus at he
      simpa only [Int.emod_eq_of_lt hz.1 hz.2, Int.emod_eq_of_lt hw.1 hw.2] using he
    · change ((D.target - D.leftResidue z.val) % D.modulus) % D.modulus =
        ((D.target - D.leftResidue w.val) % D.modulus) % D.modulus at he
      simp only [Int.emod_emod] at he
      have hh := congrArg (fun x : ℤ => (D.target - x) % D.modulus) he
      simp only [Int.sub_emod_emod, sub_sub_cancel] at hh
      simpa only [Int.emod_eq_of_lt hz.1 hz.2, Int.emod_eq_of_lt hw.1 hw.2] using hh
  have hp : (0 : ℤ) < D.p0 := by exact_mod_cast D.p0_positive
  simp only [leftResidue] at hleft
  have heval : (z.val : ℤ) = w.val :=
    mul_left_cancel₀ hp.ne' (add_left_cancel hleft)
  exact Fin.ext (by exact_mod_cast heval)

theorem parentUniverses_disjoint (side : Fin 2) :
    Pairwise (fun z w : Fin D.q =>
      Disjoint (D.parentData side z.val).entryUniverse (D.parentData side w.val).entryUniverse) := by
  classical
  let : DecidableEq (Entry (Fin n)) := fun _ _ => Classical.propDecidable _
  intro z w hne
  apply Finset.disjoint_left.mpr
  intro e hez hew
  have hz := (D.parentData side z.val).rawEntries_parent_mod e (List.mem_toFinset.mp hez)
  have hw := (D.parentData side w.val).rawEntries_parent_mod e (List.mem_toFinset.mp hew)
  exact hne (D.parentResidue_injective side (hz.symm.trans hw))

theorem sum_parentUniverse_card (side : Fin 2) :
    ∑ z : Fin D.q, (D.parentData side z.val).entryUniverse.card ≤
      (D.lowEntryUniverse side).card := by
  classical
  have hd : ((Finset.univ : Finset (Fin D.q)) : Set (Fin D.q)).PairwiseDisjoint
      (fun z => (D.parentData side z.val).entryUniverse) := by
    intro z _ w _ hne
    exact D.parentUniverses_disjoint side hne
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro e he
  obtain ⟨z, _, he⟩ := Finset.mem_biUnion.mp he
  exact D.entryUniverse_subset_low side z.val MaskRestriction.empty he

end RepresentationScheduleData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)
variable (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
variable (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
variable (q : ℕ) (hq : 0 < q)

theorem schedule_lowEntryUniverse_card (side : Fin 2) :
    ((R.scheduleData h r hn hlog q hq).lowEntryUniverse side).card =
      if side = 0 then RepresentationMoments.UL (prefixModulus_pos h.2 0)
        (R.signedWeights h.1.1.1)
        (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) 0) r
      else RepresentationMoments.UR (prefixModulus_pos h.2 0)
        (R.signedWeights h.1.1.1)
        (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) 1)
        (R.signedTarget h.1.1.1) r := by
  classical
  fin_cases side
  all_goals
    simp only [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl,
      show (⟨1, by decide⟩ : Fin 2) = 1 from rfl, ite_true,
      ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    apply congrArg Finset.card
    ext e
    simp only [RepresentationScheduleData.lowEntryUniverse, residueFiltered, Finset.mem_filter,
      normalizedResidue_eq_iff, ResidueMatchAccounting.complement_val]
  · change (_ ∧ e.value % (prefixModulus h.2.val 0 : ℤ) =
        (r.1.val : ℤ) % (prefixModulus h.2.val 0 : ℤ)) ↔ (_ ∧
        e.value % (prefixModulus h.2.val 0 : ℤ) = (r.1.val : ℤ))
    have hr : (r.1.val : ℤ) % (prefixModulus h.2.val 0 : ℤ) = r.1.val :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.1.isLt)
    rw [hr]
    rfl
  · rfl


/-- Over the entire residue loop the prefix account uses one low-entry
universe, rather than charging it once per extra-prime residue. -/
theorem schedule_taskStarts_sum_bound (B : ℕ) (side : Fin 2) :
    compressionDictionaryCapacity n *
      (∑ z : Fin q, ((R.scheduleData h r hn hlog q hq).parentData side z.val).taskStarts B
        (R.scheduleData h r hn hlog q hq).topOrder MaskRestriction.empty) ≤
      q * compressionDictionaryCapacity n + 2 * (mixerSize n + 1) *
        ((R.scheduleData h r hn hlog q hq).lowEntryUniverse side).card := by
  have hs := Finset.sum_le_sum (fun (z : Fin q) (_ : z ∈ Finset.univ) =>
    R.schedule_taskStarts_bound h r hn hlog q hq z.val B side)
  have hu := (R.scheduleData h r hn hlog q hq).sum_parentUniverse_card side
  calc
    _ = ∑ z : Fin q, compressionDictionaryCapacity n *
        ((R.scheduleData h r hn hlog q hq).parentData side z.val).taskStarts B
          (R.scheduleData h r hn hlog q hq).topOrder MaskRestriction.empty :=
      by rw [Finset.mul_sum]
    _ ≤ ∑ z : Fin q, (compressionDictionaryCapacity n + 2 * (mixerSize n + 1) *
        ((R.scheduleData h r hn hlog q hq).parentData side z.val).entryUniverse.card) := hs
    _ = q * compressionDictionaryCapacity n + 2 * (mixerSize n + 1) *
        ∑ z : Fin q, ((R.scheduleData h r hn hlog q hq).parentData side z.val).entryUniverse.card := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ hu) _

theorem schedule_checkInputSize_sum_bound (B : ℕ) :
    (∑ z : Fin q, TopCoordinates.checkInputSize
      (((R.scheduleData h r hn hlog q hq).bucket z.val).checkList B)) ≤
      ((R.scheduleData h r hn hlog q hq).lowEntryUniverse 0).card +
        (2 * mixerSize n + 3) * ((R.scheduleData h r hn hlog q hq).lowEntryUniverse 1).card := by
  have hs := Finset.sum_le_sum (fun (z : Fin q) (_ : z ∈ Finset.univ) =>
    R.schedule_checkInputSize_bound h r hn hlog q hq z.val B)
  have hL := (R.scheduleData h r hn hlog q hq).sum_parentUniverse_card 0
  have hR := (R.scheduleData h r hn hlog q hq).sum_parentUniverse_card 1
  calc
    _ ≤ ∑ z : Fin q,
        (((R.scheduleData h r hn hlog q hq).parentData 0 z.val).entryUniverse.card +
          (2 * mixerSize n + 3) *
            ((R.scheduleData h r hn hlog q hq).parentData 1 z.val).entryUniverse.card) := hs
    _ = (∑ z : Fin q,
        ((R.scheduleData h r hn hlog q hq).parentData 0 z.val).entryUniverse.card) +
      (2 * mixerSize n + 3) * ∑ z : Fin q,
        ((R.scheduleData h r hn hlog q hq).parentData 1 z.val).entryUniverse.card := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := Nat.add_le_add hL (Nat.mul_le_mul_left _ hR)

/-- The resource event was sampled before the extra prime and bounds every
full-loop universe, without assuming that the representation survives. -/
theorem schedule_lowEntryUniverse_resource (hlarge : 20000 ≤ n)
    (hgood : R.AllocatedResourceGood hlarge hlog ⟨h, r⟩) (side : Fin 2) :
    (((R.scheduleData h r hn hlog q hq).lowEntryUniverse side).card : ℝ) ≤
      (inputScale R.input : ℝ) ^ 200 * (2 : ℝ) ^ R.resourceLambda h.1.1.1 h.1.1.2 := by
  rw [R.schedule_lowEntryUniverse_card h r hn hlog q hq side]
  fin_cases side
  · exact hgood.2.2.1
  · exact hgood.2.2.2

theorem schedule_mean_allScans (B u : ℕ) (hu : 256 ≤ u) (hnu : n ≤ u)
    (hgu : 2 * blockHalf n 0 + 1 ≤ u) :
    let S := separatorParameters h.1.1.2 (by omega)
    RepresentationMoments.mean (fun draws : SeparatorExpectation.IndependentFamilies
      (2 * blockHalf n 0) S.e S.counts =>
      (((∑ z : Fin q, (R.topCoordinates h.1.1.1 h.1.2).totalScans
        (SeparatorExpectation.familyArrays draws) (R.signedTarget h.1.1.1)
        (((R.scheduleData h r hn hlog q hq).bucket z.val).checkList B)) : ℕ) : ℝ)) ≤
      ((((R.scheduleData h r hn hlog q hq).lowEntryUniverse 0).card + (2 * mixerSize n + 3) *
        ((R.scheduleData h r hn hlog q hq).lowEntryUniverse 1).card : ℕ) : ℝ) *
        (u : ℝ) ^ 22 * (2 : ℝ) ^ (((4 * (2 * blockHalf n 0) : ℕ) : ℝ) *
          (1 - binaryEntropy (1 / 4))) := by
  dsimp only
  simp only [Nat.cast_sum]
  rw [SeparatorExpectation.mean_sum]
  have hs := Finset.sum_le_sum (fun (z : Fin q) (_ : z ∈ Finset.univ) =>
    R.schedule_mean_totalScans h r hn hlog q hq z.val B u hu hnu hgu)
  apply hs.trans
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast R.schedule_checkInputSize_sum_bound h r hn hlog q hq B

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
