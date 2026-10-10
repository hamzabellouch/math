import OAI.NumberTheory.EgyptianFractions.Defs
import OAI.NumberTheory.EgyptianFractions.FiniteExpansion

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

private def pronic (j : ℕ) : ℕ := (j + 1) * (j + 2)

private theorem pronic_strictMono : StrictMono pronic := by
  intro a b hab
  unfold pronic
  nlinarith

private theorem pronic_pos (j : ℕ) : 0 < pronic j := by
  unfold pronic
  positivity

private theorem reciprocal_pronic (j : ℕ) :
    (1 : ℚ) / pronic j = 1 / (j + 1 : ℚ) - 1 / (j + 2 : ℚ) := by
  have h1 : (j + 1 : ℚ) ≠ 0 := by positivity
  have h2 : (j + 2 : ℚ) ≠ 0 := by positivity
  simp only [pronic, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  ring

private theorem sum_reciprocal_pronic (t : ℕ) :
    (∑ j ∈ Finset.range t, (1 : ℚ) / pronic j) = 1 - 1 / (t + 1 : ℚ) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, reciprocal_pronic]
    push_cast
    ring

private def pronicSet (m : ℕ) : Finset ℕ :=
  (Finset.range (m - 1)).image pronic

private theorem pronicSet_pos {m d : ℕ} (hd : d ∈ pronicSet m) : 1 ≤ d := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
  exact pronic_pos j

private theorem pronicSet_sum {m : ℕ} (hm : 1 ≤ m) :
    (∑ d ∈ pronicSet m, (1 : ℚ) / d) = 1 - 1 / (m : ℚ) := by
  unfold pronicSet
  rw [Finset.sum_image]
  · rw [sum_reciprocal_pronic]
    congr 2
    norm_cast
    omega
  · intro a ha b hb hab
    exact pronic_strictMono.injective hab

private theorem pronic_succ_not_pronic {a b : ℕ} : pronic a + 1 ≠ pronic b := by
  intro h
  rcases lt_trichotomy a b with hab | hab | hab
  · have : a + 1 ≤ b := hab
    unfold pronic at h
    nlinarith
  · subst b
    omega
  · have := pronic_strictMono hab
    omega

private theorem insert_pronicSet_one {m : ℕ} (hm : 1 ≤ m)
    (hmem : m ∉ pronicSet m) :
    (∀ d ∈ insert m (pronicSet m), 1 ≤ d) ∧
      (∑ d ∈ insert m (pronicSet m), (1 : ℚ) / d) = 1 := by
  constructor
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hm
    · exact pronicSet_pos hd
  · rw [Finset.sum_insert hmem, pronicSet_sum hm]
    ring

private theorem insert_pronicSet_card {m : ℕ} (hm : 1 ≤ m)
    (hmem : m ∉ pronicSet m) : (insert m (pronicSet m)).card = m := by
  rw [Finset.card_insert_of_notMem hmem]
  unfold pronicSet
  rw [Finset.card_image_of_injective _ pronic_strictMono.injective, Finset.card_range]
  omega

/-- Every integer at least two occurs in a finite distinct unit fraction expansion of one.
The construction telescopes consecutive reciprocal differences. -/
theorem exists_finset_one_with_marker_bounded (m : ℕ) (hm : 2 ≤ m) :
    ∃ s : Finset ℕ, (∀ d ∈ s, 1 ≤ d) ∧ m ∈ s ∧
      (∑ d ∈ s, (1 : ℚ) / d) = 1 ∧ s.card ≤ m + 1 := by
  classical
  by_cases hmem : m ∈ pronicSet m
  · obtain ⟨a, ha, ham⟩ := Finset.mem_image.mp hmem
    have hnext : m + 1 ∉ pronicSet (m + 1) := by
      intro h
      obtain ⟨b, hb, hbm⟩ := Finset.mem_image.mp h
      apply pronic_succ_not_pronic (a := a) (b := b)
      omega
    obtain ⟨hpos, hsum⟩ := insert_pronicSet_one (by omega : 1 ≤ m + 1) hnext
    refine ⟨insert (m + 1) (pronicSet (m + 1)), hpos, ?_, hsum, ?_⟩
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨a, ?_, ham⟩
      apply Finset.mem_range.mpr
      have := Finset.mem_range.mp ha
      omega
    · exact (insert_pronicSet_card (by omega : 1 ≤ m + 1) hnext).le
  · obtain ⟨hpos, hsum⟩ := insert_pronicSet_one (by omega : 1 ≤ m) hmem
    refine ⟨insert m (pronicSet m), hpos, by simp, hsum, ?_⟩
    rw [insert_pronicSet_card (by omega : 1 ≤ m) hmem]
    omega

/-- The finite-set version of exact-marker occurrence. -/
theorem exists_finset_one_with_marker (m : ℕ) (hm : 2 ≤ m) :
    ∃ s : Finset ℕ, (∀ d ∈ s, 1 ≤ d) ∧ m ∈ s ∧
      (∑ d ∈ s, (1 : ℚ) / d) = 1 := by
  obtain ⟨s, hpos, hmem, hsum, _⟩ := exists_finset_one_with_marker_bounded m hm
  exact ⟨s, hpos, hmem, hsum⟩

/-- The telescoping construction uses at most one more term than the marker. -/
theorem every_exact_marker_occurs_bounded (m : ℕ) (hm : 2 ≤ m) :
    ∃ k : ℕ, k ≤ m + 1 ∧ m ∈ D k := by
  obtain ⟨s, hpos, hmem, hsum, hcard⟩ := exists_finset_one_with_marker_bounded m hm
  obtain ⟨n, hnpos, hnmono, hnsum, hnmem⟩ :=
    finset_unit_fraction_representation s 1 1 hpos hsum
  exact ⟨s.card, hcard, hm, n, ⟨hnpos, hnmono, hnsum⟩, (hnmem m).mpr hmem⟩

/-- Unconditional exact-marker occurrence, in the qualified expansion model. -/
theorem every_exact_marker_occurs_proof :
    ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k := by
  intro m hm
  obtain ⟨s, hpos, hmem, hsum⟩ := exists_finset_one_with_marker m hm
  obtain ⟨n, hnpos, hnmono, hnsum, hnmem⟩ :=
    finset_unit_fraction_representation s 1 1 hpos hsum
  exact ⟨s.card, hm, n, ⟨hnpos, hnmono, hnsum⟩, (hnmem m).mpr hmem⟩

end Problem337

end

end OAI
