import OAI.Probability.InvariantIsing.Fields.SpinHammingEnergy

namespace OAI

/-! Attainability of every positive-spin count and deterministic projection
to a nearest magnetization slice. -/

noncomputable section
open scoped BigOperators symmDiff

namespace InvariantIsing

def spinPositiveSites {N : ℕ} (σ : Spin N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => σ i = true)

def spinOfPositiveSites {N : ℕ} (S : Finset (Fin N)) : Spin N :=
  fun i => decide (i ∈ S)

@[simp] lemma spinPositiveSites_of_set {N : ℕ} (S : Finset (Fin N)) :
    spinPositiveSites (spinOfPositiveSites S) = S := by
  ext i
  simp [spinPositiveSites, spinOfPositiveSites]

@[simp] lemma spinOfPositiveSites_of_spin {N : ℕ} (σ : Spin N) :
    spinOfPositiveSites (spinPositiveSites σ) = σ := by
  funext i
  cases hσ : σ i <;> simp [spinPositiveSites, spinOfPositiveSites, hσ]

lemma spin_hamming_eq_symmDiff {N : ℕ} (σ τ : Spin N) :
    hammingDist σ τ = (spinPositiveSites σ ∆ spinPositiveSites τ).card := by
  unfold hammingDist
  congr 1
  ext i
  cases hσ : σ i <;> cases hτ : τ i <;>
    simp [spinPositiveSites, hσ, hτ, Finset.mem_symmDiff]

lemma exists_spin_with_count_nearest {N : ℕ} (σ : Spin N) (k : ℕ) (hk : k ≤ N) :
    ∃ τ : Spin N, (spinPositiveSites τ).card = k ∧
      hammingDist σ τ = (spinPositiveSites σ).card - k + (k - (spinPositiveSites σ).card) := by
  classical
  let A := spinPositiveSites σ
  by_cases hka : k ≤ A.card
  · obtain ⟨T, hTA, hT⟩ := Finset.exists_subset_card_eq hka
    refine ⟨spinOfPositiveSites T, by simpa using hT, ?_⟩
    rw [spin_hamming_eq_symmDiff, spinPositiveSites_of_set]
    change (A ∆ T).card = A.card - k + (k - A.card)
    rw [Finset.symmDiff_def, Finset.sdiff_eq_empty_iff_subset.mpr hTA,
      Finset.union_empty, Finset.card_sdiff_of_subset hTA, hT, Nat.sub_eq_zero_of_le hka,
      Nat.add_zero]
  · have hak : A.card ≤ k := (Nat.le_of_lt (Nat.lt_of_not_ge hka))
    have hrem : k - A.card ≤ (Finset.univ \ A).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ,
        Fintype.card_fin]
      omega
    obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq hrem
    have hd : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      exact (Finset.mem_sdiff.mp (hB hiB)).2 hiA
    have hT : (A ∪ B).card = k := by
      rw [Finset.card_union_of_disjoint hd, hBc]
      omega
    refine ⟨spinOfPositiveSites (A ∪ B), by simpa using hT, ?_⟩
    rw [spin_hamming_eq_symmDiff, spinPositiveSites_of_set]
    change (A ∆ (A ∪ B)).card = A.card - k + (k - A.card)
    rw [Finset.symmDiff_def,
      Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_left,
      Finset.empty_union, Finset.card_sdiff_of_subset Finset.subset_union_left, hT,
      Nat.sub_eq_zero_of_le hak, Nat.zero_add]

def spinCountProjection {N : ℕ} (k : ℕ) (hk : k ≤ N) (σ : Spin N) : Spin N :=
  Classical.choose (exists_spin_with_count_nearest σ k hk)

lemma spinCountProjection_count {N : ℕ} (k : ℕ) (hk : k ≤ N) (σ : Spin N) :
    (spinPositiveSites (spinCountProjection k hk σ)).card = k :=
  (Classical.choose_spec (exists_spin_with_count_nearest σ k hk)).1

lemma spinCountProjection_distance {N : ℕ} (k : ℕ) (hk : k ≤ N) (σ : Spin N) :
    hammingDist σ (spinCountProjection k hk σ) =
      (spinPositiveSites σ).card - k + (k - (spinPositiveSites σ).card) :=
  (Classical.choose_spec (exists_spin_with_count_nearest σ k hk)).2

def spinCountSlice (N k : ℕ) : Finset (Spin N) :=
  Finset.univ.filter (fun σ => (spinPositiveSites σ).card = k)

lemma spinCountSlice_nonempty {N k : ℕ} (hk : k ≤ N) : (spinCountSlice N k).Nonempty := by
  let σ : Spin N := fun _ => false
  refine ⟨spinCountProjection k hk σ, ?_⟩
  simp only [spinCountSlice, Finset.mem_filter, Finset.mem_univ, true_and,
    spinCountProjection_count]

lemma spinCountProjection_mem {N k : ℕ} (hk : k ≤ N) (σ : Spin N) :
    spinCountProjection k hk σ ∈ spinCountSlice N k := by
  simp only [spinCountSlice, Finset.mem_filter, Finset.mem_univ, true_and,
    spinCountProjection_count]

end InvariantIsing

end

end OAI
