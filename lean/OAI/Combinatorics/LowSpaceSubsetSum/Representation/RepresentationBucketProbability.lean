import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBucketBounds

namespace OAI

/-! # Actual low-entry universes and extra-prime collision expectations -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

private theorem residueFiltered_eq_mod_filter {α : Type*} {p : ℕ} (hp : 0 < p)
    (X : Finset α) (value : α → ℤ) (r : Fin p) :
    residueFiltered hp X value r = X.filter (fun x => value x % (p : ℤ) = (r.val : ℤ) % p) := by
  classical
  ext x
  simp only [residueFiltered, Finset.mem_filter, normalizedResidue_eq_iff]
  rw [Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ r.val) (by exact_mod_cast r.isLt)]

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- The actual distinct-entry universe after only the parent low filter. -/
def chosenLowEntries (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j : Fin 2) :
    Finset (Entry (Fin n)) :=
  (RepresentationUniverse.validEntries (R.signedWeights h.1.1.1)
    (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) j)).filter
      (fun e => e.value % (prefixModulus h.2.val 0 : ℤ) =
        weight (R.signedWeights h.1.1.1) (R.chosenNamedParent h r hn hlog j) %
          (prefixModulus h.2.val 0 : ℤ))

theorem chosenLowEntries_subset (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j : Fin 2) :
    R.chosenLowEntries h r hn hlog j ⊆
      RepresentationUniverse.validEntries (R.signedWeights h.1.1.1)
        (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) j) :=
  Finset.filter_subset _ _

theorem chosenEntry_lowEntries (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) (j : Fin 2) :
    RepresentationUniverse.entry (R.signedWeights h.1.1.1) (R.chosenRawParent h r hn hlog j) ∈
      R.chosenLowEntries h r hn hlog j := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨R.chosenEntry_mem (R.allocatedChildAssignment hn hlog) h r hr _ j,
    congrArg (fun w : ℤ => w % (prefixModulus h.2.val 0 : ℤ))
      (R.chosenRawParent_weight h r hn hlog hr j)⟩

theorem chosenLowEntries_card (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) (j : Fin 2) :
    (R.chosenLowEntries h r hn hlog j).card =
      if j = 0 then RepresentationMoments.UL (prefixModulus_pos h.2 0)
        (R.signedWeights h.1.1.1)
        (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) 0) r
      else RepresentationMoments.UR (prefixModulus_pos h.2 0)
        (R.signedWeights h.1.1.1)
        (R.rawLeaf h.1.1.1 h.1.1.2 h.1.2 (R.allocatedBackground h.1.1.1 h.1.1.2 hn hlog) 1)
        (R.signedTarget h.1.1.1) r := by
  classical
  have hf := R.actualFilters_of_hits (R.allocatedChildAssignment hn hlog) hr
  fin_cases j
  · simp only [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl]
    apply congrArg Finset.card
    ext e
    simp only [chosenLowEntries, Finset.mem_filter,
      residueFiltered_eq_mod_filter, chosenNamedParent, ite_true]
    rw [hf.1]
  · simp only [show (⟨1, by decide⟩ : Fin 2) = 1 from rfl,
      ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    apply congrArg Finset.card
    ext e
    simp only [chosenLowEntries, Finset.mem_filter,
      residueFiltered_eq_mod_filter, chosenNamedParent, ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
      ResidueMatchAccounting.complement_val, Int.emod_emod]
    rw [hf.2.1]

/-- Different-weight entries in the designated full parent bucket. -/
def chosenOtherBucket (h : R.PrimeHistory) (r : R.Residues h.2) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j : Fin 2) (q : ℕ) :
    Finset (Entry (Fin n)) :=
  otherCollisionKeys (R.chosenLowEntries h r hn hlog j) Entry.value
    (fun w => w % ((prefixModulus h.2.val 0 : ℤ) * q))
    (RepresentationUniverse.entry (R.signedWeights h.1.1.1) (R.chosenRawParent h r hn hlog j))

/-- Linearity of expectation counts actual distinct keys, including repeated
weights with different masks. The nonzero differences meet the input bit bound. -/
theorem chosenOtherBucket_expectation (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) (j : Fin 2) :
    (∑ q ∈ primeRange (R.extraPrimeParameter h.1.1.1),
      primeProbability (R.extraPrimeParameter h.1.1.1) q *
        (R.chosenOtherBucket h r hn hlog j q).card) ≤
      (inputScale R.input : ℝ) ^ 3 / (2 : ℝ) ^ R.extraPrimeRate h.1.1.1 *
        (R.chosenLowEntries h r hn hlog j).card := by
  apply expected_otherCollisionKeys_le _ _ _ _ _ (R.chosenEntry_lowEntries h r hn hlog hr j)
    (by positivity)
  apply R.extraPrime_product_collision _ (by omega)
  intro x hx y hy
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hy
  exact relevant_difference_bits R.input
    (R.raw_validEntries_bounded _ _ _ _ j e (R.chosenLowEntries_subset h r hn hlog j he))
    (R.raw_validEntries_bounded _ _ _ _ j f (R.chosenLowEntries_subset h r hn hlog j hf))

theorem chosenLowEntries_resource_bound (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h r)
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩) (j : Fin 2) :
    ((R.chosenLowEntries h r (by omega) hlog j).card : ℝ) ≤
      (inputScale R.input : ℝ) ^ 200 * (2 : ℝ) ^ R.resourceLambda h.1.1.1 h.1.1.2 := by
  rw [R.chosenLowEntries_card h r (by omega) hlog hr j]
  fin_cases j
  · exact hgood.2.2.1
  · exact hgood.2.2.2

/-- The resource event bounds each designated different-weight bucket
expectation by `u^203 2^(Lambda-x)`. -/
theorem chosenOtherBucket_resource_expectation (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h r)
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩) (j : Fin 2) :
    (∑ q ∈ primeRange (R.extraPrimeParameter h.1.1.1),
      primeProbability (R.extraPrimeParameter h.1.1.1) q *
        (R.chosenOtherBucket h r (by omega) hlog j q).card) ≤
      (inputScale R.input : ℝ) ^ 203 *
        (2 : ℝ) ^ (R.resourceLambda h.1.1.1 h.1.1.2 - R.extraPrimeRate h.1.1.1) := by
  apply (R.chosenOtherBucket_expectation h r (by omega) hlog hr j).trans
  apply (mul_le_mul_of_nonneg_left
    (R.chosenLowEntries_resource_bound h r hn hlog hr hgood j) (by positivity)).trans_eq
  rw [Real.rpow_sub (by norm_num)]
  have he : (inputScale R.input : ℝ) ^ 203 =
      (inputScale R.input : ℝ) ^ 3 * (inputScale R.input : ℝ) ^ 200 := by
    rw [← pow_add]
  rw [he]
  ring

/-- Both different-weight counts are controlled by one finite Markov bound;
there is no independence assertion between the two parent sides. -/
theorem chosenOtherBuckets_probability (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h r)
    (hgood : R.AllocatedResourceGood hn hlog ⟨h, r⟩) :
    1 - 4 * (inputScale R.input : ℝ) ^ 203 *
        (2 : ℝ) ^ (R.resourceLambda h.1.1.1 h.1.1.2 - R.extraPrimeRate h.1.1.1) /
          (compressionDictionaryCapacity n : ℝ) ≤
      ∑ q ∈ (primeRange (R.extraPrimeParameter h.1.1.1)).filter (fun q =>
        ((R.chosenOtherBucket h r (by omega) hlog 0 q).card : ℝ) ≤
          (compressionDictionaryCapacity n : ℝ) / 2 ∧
        ((R.chosenOtherBucket h r (by omega) hlog 1 q).card : ℝ) ≤
          (compressionDictionaryCapacity n : ℝ) / 2),
        primeProbability (R.extraPrimeParameter h.1.1.1) q := by
  let seeds := primeRange (R.extraPrimeParameter h.1.1.1)
  let prob := primeProbability (R.extraPrimeParameter h.1.1.1)
  let count := fun q => (R.chosenOtherBucket h r (by omega) hlog 0 q).card +
    (R.chosenOtherBucket h r (by omega) hlog 1 q).card
  have hmean : (∑ q ∈ seeds, prob q * (count q : ℝ)) ≤
      2 * ((inputScale R.input : ℝ) ^ 203 *
        (2 : ℝ) ^ (R.resourceLambda h.1.1.1 h.1.1.2 - R.extraPrimeRate h.1.1.1)) := by
    simp only [count, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    linarith [R.chosenOtherBucket_resource_expectation h r hn hlog hr hgood 0,
      R.chosenOtherBucket_resource_expectation h r hn hlog hr hgood 1]
  have hC : (0 : ℝ) < compressionDictionaryCapacity n := by
    exact_mod_cast (show 0 < compressionDictionaryCapacity n by
      unfold compressionDictionaryCapacity; positivity)
  have hp := probability_count_le seeds prob count
    (fun _ _ => by unfold prob primeProbability; positivity)
    (primeProbability_sum (R.extraPrimeParameter_range h.1.1.1 (by omega)).1)
    (by positivity : (0 : ℝ) < (compressionDictionaryCapacity n : ℝ) / 2) hmean
  have he : 2 * ((inputScale R.input : ℝ) ^ 203 *
      (2 : ℝ) ^ (R.resourceLambda h.1.1.1 h.1.1.2 - R.extraPrimeRate h.1.1.1)) /
        ((compressionDictionaryCapacity n : ℝ) / 2) =
      4 * (inputScale R.input : ℝ) ^ 203 *
      (2 : ℝ) ^ (R.resourceLambda h.1.1.1 h.1.1.2 - R.extraPrimeRate h.1.1.1) /
        (compressionDictionaryCapacity n : ℝ) := by ring
  rw [he] at hp
  apply hp.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨hq, hcount⟩ := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨hq, ?_, ?_⟩
    · have hle : ((R.chosenOtherBucket h r (by omega) hlog 0 q).card : ℝ) ≤ count q := by
        exact_mod_cast Nat.le_add_right _ _
      exact hle.trans hcount
    · have hle : ((R.chosenOtherBucket h r (by omega) hlog 1 q).card : ℝ) ≤ count q := by
        exact_mod_cast Nat.le_add_left _ _
      exact hle.trans hcount
  · intro _ _ _
    unfold prob primeProbability
    positivity


end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
