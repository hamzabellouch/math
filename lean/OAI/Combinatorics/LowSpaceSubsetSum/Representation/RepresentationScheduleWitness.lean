import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSchedule
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBucketWitness
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ModularFilters

namespace OAI

/-! # The successful analysis bucket is visited by the input-only loop -/

noncomputable section

namespace LowSpaceSubsetSum

theorem lifted_emod_exists {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (rho : Fin p) (a : ℤ) (ha : a % (p : ℤ) = rho.val) :
    ∃ z : ℕ, z < q ∧ a % ((p : ℤ) * q) = (rho.val : ℤ) + (p : ℤ) * z := by
  have hP : 0 < p * q := Nat.mul_pos hp hq
  let r := normalizedResidue hP a
  have hr : r.val < p * q := r.isLt
  have hbase : r.val % p = rho.val := by
    have he : ((r.val % p : ℕ) : ℤ) = (rho.val : ℤ) := by
      rw [Int.natCast_emod, normalizedResidue_cast]
      rw [Nat.cast_mul, Int.emod_emod_of_dvd a (dvd_mul_right (p : ℤ) (q : ℤ))]
      exact ha
    exact_mod_cast he
  obtain ⟨z, ⟨hz, he⟩, _⟩ := lift_residue_exists_unique hp hr hbase
  refine ⟨z, hz, ?_⟩
  have heR : (r.val : ℤ) = (rho.val : ℤ) + (p : ℤ) * z := by exact_mod_cast he
  simpa only [r, normalizedResidue_cast, Nat.cast_mul] using heR

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def scheduleData (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (q : ℕ) (hq : 0 < q) : RepresentationScheduleData n (2 * blockHalf n 0) where
  input := R.input
  signs := R.signMask h.1.1.1
  leaves := R.rawLeaf h.1.1.1 h.1.1.2 h.1.2
    (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog)
  lowModuli j := prefixModulus h.2.val j.succ
  firstResidues j := if j = 0 then r.2.1.val else r.2.2.val
  p0 := prefixModulus h.2.val 0
  p0_positive := prefixModulus_pos h.2 0
  q := q
  q_positive := hq
  rho0 := r.1
  capacity := compressionDictionaryCapacity n
  coordinates := R.topCoordinates h.1.1.1 h.1.2
  topOrder := (R.orderedMixers h.1.1.1 0).sort (· ≤ ·)

theorem chosen_left_lift (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (q : ℕ) (hq : 0 < q) :
    ∃ z : ℕ, z < q ∧ (R.scheduleData h r hn hlog q hq).leftResidue z =
      (R.chosenEntry h r hn hlog 0).value % ((prefixModulus h.2.val 0 : ℤ) * q) := by
  have hf := (R.chosen_raw_filters h r hn hlog hr).1
  have ha : (R.chosenEntry h r hn hlog 0).value % (prefixModulus h.2.val 0 : ℤ) =
      (r.1.val : ℤ) := by
    change RepresentationUniverse.parentWeight (R.signedWeights h.1.1.1)
      (R.chosenRawParent h r hn hlog 0) % (prefixModulus h.2.val 0 : ℤ) = (r.1.val : ℤ)
    change RepresentationUniverse.parentWeight (R.signedWeights h.1.1.1)
      (R.chosenRawParent h r hn hlog 0) % (prefixModulus h.2.val 0 : ℤ) =
        (r.1.val : ℤ) % (prefixModulus h.2.val 0 : ℤ) at hf
    have he : (r.1.val : ℤ) % (prefixModulus h.2.val 0 : ℤ) = r.1.val :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.1.isLt)
    rwa [he] at hf
  obtain ⟨z, hz, he⟩ := lifted_emod_exists (prefixModulus_pos h.2 0) hq r.1
    (R.chosenEntry h r hn hlog 0).value ha
  exact ⟨z, hz, he.symm⟩

theorem schedule_chosen_parent_eq (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (q : ℕ) (hq : 0 < q) (z : ℕ)
    (hz : (R.scheduleData h r hn hlog q hq).leftResidue z =
      (R.chosenEntry h r hn hlog 0).value % ((prefixModulus h.2.val 0 : ℤ) * q))
    (j : Fin 2) :
    (R.scheduleData h r hn hlog q hq).parentData j z =
      R.chosenParentData h r hn hlog j ((prefixModulus h.2.val 0 : ℤ) * q)
        (by exact (R.scheduleData h r hn hlog q hq).modulus_positive)
        (compressionDictionaryCapacity n) MaskRestriction.empty := by
  have hweight (j : Fin 2) := R.chosenRawParent_weight h r hn hlog hr j
  have hmatch : (R.chosenEntry h r hn hlog 0).value +
      (R.chosenEntry h r hn hlog 1).value = R.signedTarget h.1.1.1 :=
    (R.chosenEntries_match h r hn hlog hr).1
  have hparent : (if j = 0 then (R.scheduleData h r hn hlog q hq).leftResidue z
      else ((R.scheduleData h r hn hlog q hq).target -
        (R.scheduleData h r hn hlog q hq).leftResidue z) %
          (R.scheduleData h r hn hlog q hq).modulus) =
      weight (R.signedWeights h.1.1.1) (R.chosenNamedParent h r hn hlog j) %
        ((prefixModulus h.2.val 0 : ℤ) * q) := by
    fin_cases j
    · change (R.scheduleData h r hn hlog q hq).leftResidue z =
        weight (R.signedWeights h.1.1.1) (R.chosenNamedParent h r hn hlog 0) %
          ((prefixModulus h.2.val 0 : ℤ) * q)
      simpa only [chosenEntry, RepresentationUniverse.entry, hweight 0] using hz
    · change ((R.scheduleData h r hn hlog q hq).target -
        (R.scheduleData h r hn hlog q hq).leftResidue z) %
          ((prefixModulus h.2.val 0 : ℤ) * q) =
        weight (R.signedWeights h.1.1.1) (R.chosenNamedParent h r hn hlog 1) %
          ((prefixModulus h.2.val 0 : ℤ) * q)
      rw [hz]
      change (R.signedTarget h.1.1.1 - (R.chosenEntry h r hn hlog 0).value %
        ((prefixModulus h.2.val 0 : ℤ) * q)) % ((prefixModulus h.2.val 0 : ℤ) * q) = _
      rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
      have he : R.signedTarget h.1.1.1 - (R.chosenEntry h r hn hlog 0).value =
          (R.chosenEntry h r hn hlog 1).value := by linarith
      rw [he]
      change RepresentationUniverse.parentWeight (R.signedWeights h.1.1.1)
        (R.chosenRawParent h r hn hlog 1) % _ = _
      rw [hweight 1]
  unfold RepresentationScheduleData.parentData chosenParentData
  dsimp only [scheduleData, RepresentationScheduleData.modulus, RepresentationScheduleData.target]
  congr 1

theorem schedule_chosen_bucket_eq (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (q : ℕ) (hq : 0 < q) (z : ℕ)
    (hz : (R.scheduleData h r hn hlog q hq).leftResidue z =
      (R.chosenEntry h r hn hlog 0).value % ((prefixModulus h.2.val 0 : ℤ) * q)) :
    (R.scheduleData h r hn hlog q hq).bucket z =
      R.chosenBucketData h r hn hlog q (by exact (R.scheduleData h r hn hlog q hq).modulus_positive) := by
  unfold RepresentationScheduleData.bucket chosenBucketData
  rw [R.schedule_chosen_parent_eq h r hn hlog hr q hq z hz 0,
    R.schedule_chosen_parent_eq h r hn hlog hr q hq z hz 1]
  rfl

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
