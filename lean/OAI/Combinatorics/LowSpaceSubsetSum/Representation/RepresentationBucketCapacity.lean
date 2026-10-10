import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBucketProbability

namespace OAI

/-! # Capacity of the actual designated parent buckets -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

private theorem hashBucket_mod_mul_low {α : Type*} (X : Finset α) (v : α → ℤ)
    (x : α) (p q : ℤ) :
    hashBucket (X.filter fun e => v e % p = v x % p) v (fun w => w % (p * q)) x =
      hashBucket X v (fun w => w % (p * q)) x := by
  classical
  ext e
  simp only [hashBucket, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, (show Int.ModEq (p * q) (v e) (v x) from h.2).of_dvd
      (show p ∣ p * q from ⟨q, rfl⟩)⟩, h.2⟩

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- The low restriction removes no member of the full product-modulus bucket. -/
theorem chosenParentBucket_eq_hashBucket (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (j : Fin 2) (q : ℕ) :
    R.chosenParentBucket h r hn hlog j ((prefixModulus h.2.val 0 : ℤ) * q) =
      hashBucket (R.chosenLowEntries h r hn hlog j) Entry.value
        (fun w => w % ((prefixModulus h.2.val 0 : ℤ) * q))
        (RepresentationUniverse.entry (R.signedWeights h.1.1.1)
          (R.chosenRawParent h r hn hlog j)) := by
  classical
  have hw := R.chosenRawParent_weight h r hn hlog hr j
  ext e
  simp only [chosenParentBucket, chosenLowEntries, hashBucket, Finset.mem_filter]
  change _ ↔ (_ ∧ _) ∧ e.value % ((prefixModulus h.2.val 0 : ℤ) * q) =
    RepresentationUniverse.parentWeight (R.signedWeights h.1.1.1) (R.chosenRawParent h r hn hlog j) %
      ((prefixModulus h.2.val 0 : ℤ) * q)
  rw [hw]
  constructor
  · intro he
    exact ⟨⟨he.1, (show Int.ModEq ((prefixModulus h.2.val 0 : ℤ) * q)
      e.value (weight (R.signedWeights h.1.1.1) (R.chosenNamedParent h r hn hlog j))
        from he.2).of_dvd ⟨q, rfl⟩⟩, he.2⟩
  · exact fun he => ⟨he.1.1, he.2⟩

/-- The unrefined left bucket fits its actual fixed-capacity dictionary. -/
theorem chosenLeftBucket_fits (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (q : ℕ)
    (hq : ((R.chosenOtherBucket h r hn hlog 0 q).card : ℝ) ≤
      (compressionDictionaryCapacity n : ℝ) / 2) :
    (R.chosenParentBucket h r hn hlog 0 ((prefixModulus h.2.val 0 : ℤ) * q)).card ≤
      compressionDictionaryCapacity n := by
  rw [R.chosenParentBucket_eq_hashBucket h r hn hlog hr 0 q, hashBucket_card]
  have he := R.left_equalWeight_half_capacity h.1.1.1 h.1.1.2 h.1.2
    (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) (by omega)
    (R.chosenLowEntries h r hn hlog 0) (R.chosenLowEntries_subset h r hn hlog 0)
    (RepresentationUniverse.entry (R.signedWeights h.1.1.1) (R.chosenRawParent h r hn hlog 0))
  have hs : ((sameWeightKeys (R.chosenLowEntries h r hn hlog 0) Entry.value
        (RepresentationUniverse.entry (R.signedWeights h.1.1.1) (R.chosenRawParent h r hn hlog 0))).card : ℝ) +
      (R.chosenOtherBucket h r hn hlog 0 q).card ≤ compressionDictionaryCapacity n := by
    linarith
  exact_mod_cast hs

/-- A full right-mask prefix has one possible equal-weight key, while its
unequal-weight keys are already counted in the unrefined collision bucket. -/
theorem chosenRightFullBucket_fits (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r)
    (q : ℕ) (D : Finset (Fin n))
    (hq : ((R.chosenOtherBucket h r hn hlog 1 q).card : ℝ) ≤
      (compressionDictionaryCapacity n : ℝ) / 2) :
    ((R.chosenParentBucket h r hn hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q)).filter
      (fun e => e.mask = D)).card ≤ compressionDictionaryCapacity n := by
  classical
  let X := R.chosenLowEntries h r hn hlog 1
  let x := RepresentationUniverse.entry (R.signedWeights h.1.1.1)
    (R.chosenRawParent h r hn hlog 1)
  let Y := X.filter fun e => e.mask = D
  have heq : ((sameWeightKeys Y Entry.value x).card : ℝ) ≤
      (compressionDictionaryCapacity n : ℝ) / 2 := by
    have hset : sameWeightKeys Y Entry.value x = X.filter (fun e => e.value = x.value ∧ e.mask = D) := by
      ext e
      simp only [sameWeightKeys, Y, Finset.mem_filter]
      tauto
    rw [hset]
    exact right_fullMask_half_capacity X x.value D (by omega)
  have hother : (otherCollisionKeys Y Entry.value
      (fun w => w % ((prefixModulus h.2.val 0 : ℤ) * q)) x).card ≤
        (R.chosenOtherBucket h r hn hlog 1 q).card := by
    apply Finset.card_le_card
    intro e he
    simp only [otherCollisionKeys, Y, Finset.mem_filter] at he
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he.1.1.1, he.1.2⟩, he.2⟩
  have hb : ((hashBucket Y Entry.value
      (fun w => w % ((prefixModulus h.2.val 0 : ℤ) * q)) x).card : ℝ) ≤
        compressionDictionaryCapacity n := by
    rw [hashBucket_card, Nat.cast_add]
    have ho : ((otherCollisionKeys Y Entry.value
      (fun w => w % ((prefixModulus h.2.val 0 : ℤ) * q)) x).card : ℝ) ≤
        (compressionDictionaryCapacity n : ℝ) / 2 :=
      le_trans (by exact_mod_cast hother) hq
    linarith
  have hset : (R.chosenParentBucket h r hn hlog 1
      ((prefixModulus h.2.val 0 : ℤ) * q)).filter (fun e => e.mask = D) =
      hashBucket Y Entry.value (fun w => w % ((prefixModulus h.2.val 0 : ℤ) * q)) x := by
    rw [R.chosenParentBucket_eq_hashBucket h r hn hlog hr 1 q]
    ext e
    simp only [hashBucket, Y, X, x, Finset.mem_filter]
    tauto
  rw [hset]
  exact_mod_cast hb

/-- Both actual bucket capacities hold for at least nine tenths of the extra
prime choices, with no independence assumption between the two counts. -/
theorem chosenBuckets_probability (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h r)
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩)
    (hs : mixerSpreadTest (R.signedWeights h.1.1.1) (R.orderedMixers h.1.1.1) n)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (D : Finset (Fin n)) :
    (9 / 10 : ℝ) ≤
      ∑ q ∈ (primeRange (R.extraPrimeParameter h.1.1.1)).filter (fun q : ℕ =>
        (R.chosenParentBucket h r (by omega) hlog 0 ((prefixModulus h.2.val 0 : ℤ) * q)).card ≤
          compressionDictionaryCapacity n ∧
        ((R.chosenParentBucket h r (by omega) hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q)).filter
          (fun e => e.mask = D)).card ≤ compressionDictionaryCapacity n),
        primeProbability (R.extraPrimeParameter h.1.1.1) q := by
  have hp := R.chosenOtherBuckets_probability h r hn hlog hr hgood
  have hloss := R.representation_bucket_loss h.1.1.1 h.1.1.2 hn hs hscale
  have hsmall : (9 / 10 : ℝ) ≤
      ∑ q ∈ (primeRange (R.extraPrimeParameter h.1.1.1)).filter (fun q : ℕ =>
        ((R.chosenOtherBucket h r (by omega) hlog 0 q).card : ℝ) ≤
          (compressionDictionaryCapacity n : ℝ) / 2 ∧
        ((R.chosenOtherBucket h r (by omega) hlog 1 q).card : ℝ) ≤
          (compressionDictionaryCapacity n : ℝ) / 2),
        primeProbability (R.extraPrimeParameter h.1.1.1) q := by linarith
  apply hsmall.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨hmem, hleft, hright⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hmem,
      R.chosenLeftBucket_fits h r (by omega) hlog hr q hleft,
      R.chosenRightFullBucket_fits h r (by omega) hlog hr q D hright⟩
  · intro _ _ _
    unfold primeProbability
    positivity

/-- The extra-prime draw is uniform on the concrete prime range. -/
abbrev ExtraPrimeSpace (z : Layout n) := ↥(primeRange (R.extraPrimeParameter z))

def extraPrimeLaw (z : Layout n) (hn : 100 ≤ n) : FiniteLaw (R.ExtraPrimeSpace z) := by
  let : Nonempty (R.ExtraPrimeSpace z) :=
    ⟨⟨(primeRange_nonempty (R.extraPrimeParameter_range z hn).1).choose,
      (primeRange_nonempty (R.extraPrimeParameter_range z hn).1).choose_spec⟩⟩
  exact FiniteLaw.uniform

theorem extraPrimeLaw_probability (z : Layout n) (hn : 100 ≤ n) (P : ℕ → Prop) [DecidablePred P] :
    (R.extraPrimeLaw z hn).probability (fun q => P q.val) =
      ∑ q ∈ (primeRange (R.extraPrimeParameter z)).filter P,
        primeProbability (R.extraPrimeParameter z) q := by
  classical
  let : Nonempty (R.ExtraPrimeSpace z) :=
    ⟨⟨(primeRange_nonempty (R.extraPrimeParameter_range z hn).1).choose,
      (primeRange_nonempty (R.extraPrimeParameter_range z hn).1).choose_spec⟩⟩
  rw [extraPrimeLaw, FiniteLaw.uniform_probability,
    finiteUniformProbability_finset (primeRange (R.extraPrimeParameter z)) P]
  simp [primeProbability, div_eq_mul_inv, mul_comm]

/-- Finite-kernel version of the two actual dictionary-capacity bounds. -/
theorem chosenBuckets_law_probability (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h r)
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩)
    (hs : mixerSpreadTest (R.signedWeights h.1.1.1) (R.orderedMixers h.1.1.1) n)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (D : Finset (Fin n)) :
    (9 / 10 : ℝ) ≤ (R.extraPrimeLaw h.1.1.1 (by omega)).probability (fun q =>
        (R.chosenParentBucket h r (by omega) hlog 0 ((prefixModulus h.2.val 0 : ℤ) * q.val)).card ≤
          compressionDictionaryCapacity n ∧
        ((R.chosenParentBucket h r (by omega) hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q.val)).filter
          (fun e => e.mask = D)).card ≤ compressionDictionaryCapacity n) := by
  classical
  let P : ℕ → Prop := fun q =>
    (R.chosenParentBucket h r (by omega) hlog 0 ((prefixModulus h.2.val 0 : ℤ) * q)).card ≤
      compressionDictionaryCapacity n ∧
    ((R.chosenParentBucket h r (by omega) hlog 1 ((prefixModulus h.2.val 0 : ℤ) * q)).filter
      (fun e => e.mask = D)).card ≤ compressionDictionaryCapacity n
  change (9 / 10 : ℝ) ≤ (R.extraPrimeLaw h.1.1.1 (by omega)).probability (fun q => P q.val)
  rw [R.extraPrimeLaw_probability h.1.1.1 (by omega) P]
  exact R.chosenBuckets_probability h r hn hlog hr hgood hs hscale D

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
