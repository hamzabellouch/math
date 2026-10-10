import OAI.NumberTheory.EgyptianFractions.Defs

namespace OAI
noncomputable section

namespace Problem337

/-- The coordinate bound also bounds every denominator occurring in an exact-length expansion. -/
theorem denominator_mem_D_le_of_bound
    (hbound : ∀ k : ℕ, ∀ n : Fin k → ℕ, IsOneExpansion n →
      ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val))
    {k m : ℕ} (hm : m ∈ D k) : m ≤ k ^ (2 ^ (k - 1)) := by
  obtain ⟨_, n, hn, i, rfl⟩ := hm
  have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
  exact (hbound k n hn i).trans
    (Nat.pow_le_pow_right hk (Nat.pow_le_pow_right (by decide) (by omega)))

/-- All first-missing-denominator semantics follow from the coordinate bound. -/
theorem missing_denominator_semantics_of_bound
    (hbound : ∀ k : ℕ, ∀ n : Fin k → ℕ, IsOneExpansion n →
      ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val)) :
    ∀ k : ℕ,
  Set.Finite (D k) ∧
  (∃ m : ℕ, m ∈ missingDenominators k) ∧
  2 ≤ v k ∧ v k ∉ D k ∧
  (∀ m : ℕ, 2 ≤ m → m < v k → m ∈ D k) ∧
  (1 ≤ k → v k ≤ 1 + k ^ (2 ^ (k - 1))) := by
  intro k
  have hD : ∀ m ∈ D k, m ≤ k ^ (2 ^ (k - 1)) :=
    fun _ hm => denominator_mem_D_le_of_bound hbound hm
  have hfinite : Set.Finite (D k) :=
    (Set.finite_Iic (k ^ (2 ^ (k - 1)))).subset hD
  have hmissing : (missingDenominators k).Nonempty := by
    refine ⟨2 + k ^ (2 ^ (k - 1)), ?_⟩
    constructor
    · simp only [Set.mem_ofPred_eq]; omega
    · intro hm; have := hD _ hm; omega
  have hv : v k ∈ missingDenominators k := csInf_mem hmissing
  refine ⟨hfinite, hmissing, hv.1, hv.2, ?_, ?_⟩
  · intro m hm hmv
    by_contra hnot
    have hmem : m ∈ missingDenominators k := ⟨hm, hnot⟩
    have hle : v k ≤ m := csInf_le' hmem
    omega
  · intro hk
    have hpow : 1 ≤ k ^ (2 ^ (k - 1)) := one_le_pow₀ hk
    have hmem : 1 + k ^ (2 ^ (k - 1)) ∈ missingDenominators k := by
      constructor
      · simp only [Set.mem_ofPred_eq]; omega
      · intro hm; have := hD _ hm; omega
    exact csInf_le' hmem

end Problem337

end

end OAI
