import OAI.Algebra.DepthFive.BalancedSchedule

namespace OAI

noncomputable section

namespace Problem335.BalancedSchedule

/-- The layer immediately left of an internal vertex. -/
def leftLayer {n : ℕ} (v : Fin (n - 1)) : Fin n := ⟨v.val, by omega⟩

/-- The layer immediately right of an internal vertex. -/
def rightLayer {n : ℕ} (v : Fin (n - 1)) : Fin n := ⟨v.val + 1, by omega⟩

lemma adjacent_left_right {n : ℕ} (v : Fin (n - 1)) :
    adjacent (leftLayer v) (rightLayer v) := Or.inl rfl

lemma internalEnds_cases {n : ℕ} {i : Fin n} {v : Fin (n - 1)}
    (hv : v ∈ internalEnds i) : leftLayer v = i ∨ rightLayer v = i := by
  rcases (Finset.mem_filter.mp hv).2 with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- Internal ends at which both incident layers have type N (`false`). -/
def nnInternalEnds {n : ℕ} (τ : Fin n → Bool) (i : Fin n) : Finset (Fin (n - 1)) :=
  (internalEnds i).filter (fun v => τ (leftLayer v) = false ∧ τ (rightLayer v) = false)

lemma nnInternalEnds_subset {n : ℕ} (τ : Fin n → Bool) (i : Fin n) :
    nnInternalEnds τ i ⊆ internalEnds i := Finset.filter_subset _ _

lemma nnInternalEnds_card_le_two {n : ℕ} (τ : Fin n → Bool) (i : Fin n) :
    (nnInternalEnds τ i).card ≤ 2 :=
  (Finset.card_le_card (nnInternalEnds_subset τ i)).trans (card_internalEnds_le_two i)

lemma nnInternalEnds_nonempty_iff {n : ℕ} (τ : Fin n → Bool) (i : Fin n)
    (hi : τ i = false) :
    (nnInternalEnds τ i).Nonempty ↔ ∃ j, adjacent i j ∧ τ j = false := by
  constructor
  · rintro ⟨v, hv⟩
    have he := (Finset.mem_filter.mp hv).1
    have ht := (Finset.mem_filter.mp hv).2
    rcases internalEnds_cases he with hleft | hright
    · refine ⟨rightLayer v, ?_, ht.2⟩
      rw [← hleft]
      exact adjacent_left_right v
    · refine ⟨leftLayer v, ?_, ht.1⟩
      rw [← hright]
      exact Or.inr rfl
  · rintro ⟨j, hij | hji, hj⟩
    · let v : Fin (n - 1) := ⟨i.val, by omega⟩
      have hleft : leftLayer v = i := Fin.ext rfl
      have hright : rightLayer v = j := Fin.ext hij
      refine ⟨v, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
      · simpa [hleft, hright] using And.intro hi hj
    · let v : Fin (n - 1) := ⟨j.val, by omega⟩
      have hleft : leftLayer v = j := Fin.ext rfl
      have hright : rightLayer v = i := Fin.ext hji
      refine ⟨v, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hji⟩
      · simpa [hleft, hright] using And.intro hj hi

/-- A nonisolated N layer has at least one NN internal end. -/
lemma one_le_nnInternalEnds_card {n : ℕ} (τ : Fin n → Bool) (i : Fin n)
    (hi : τ i = false) (hnot : ¬ ∀ j, adjacent i j → τ j = true) :
    1 ≤ (nnInternalEnds τ i).card := by
  apply Finset.card_pos.mpr
  apply (nnInternalEnds_nonempty_iff τ i hi).mpr
  push Not at hnot
  rcases hnot with ⟨j, hadj, hj⟩
  exact ⟨j, hadj, by cases h : τ j <;> simp_all⟩

lemma nnInternalEnds_eq_empty_of_all_neighbors_D {n : ℕ} (τ : Fin n → Bool)
    (i : Fin n) (hi : τ i = false) (hall : ∀ j, adjacent i j → τ j = true) :
    nnInternalEnds τ i = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rw [nnInternalEnds_nonempty_iff τ i hi]
  rintro ⟨j, hadj, hj⟩
  have h := hall j hadj
  simp [hj] at h

lemma nnInternalEnds_disjoint {k : ℕ} (hk : 0 < k) (s : ℕ)
    (τ : Fin (2 * k + s) → Bool) {i j : Fin (2 * k + s)}
    (hi : i ∈ vLayers hk s) (hj : j ∈ vLayers hk s) (hne : i ≠ j) :
    Disjoint (nnInternalEnds τ i) (nnInternalEnds τ j) :=
  (vLayers_internalEnds_disjoint hk s hi hj hne).mono
    (nnInternalEnds_subset τ i) (nnInternalEnds_subset τ j)

lemma adjacent_symm {n : ℕ} {i j : Fin n} (h : adjacent i j) : adjacent j i := h.symm

/-- The coincidence set depends only on the layer and its immediate neighbors. -/
lemma nnInternalEnds_congr {n : ℕ} {τ υ : Fin n → Bool} (i : Fin n)
    (hsame : τ i = υ i) (hadj : ∀ j, adjacent i j → τ j = υ j) :
    nnInternalEnds τ i = nnInternalEnds υ i := by
  apply Finset.ext
  intro v
  simp only [nnInternalEnds, Finset.mem_filter]
  by_cases hv : v ∈ internalEnds i
  · have hl : τ (leftLayer v) = υ (leftLayer v) := by
      rcases internalEnds_cases hv with hleft | hright
      · simpa [hleft] using hsame
      · apply hadj
        rw [← hright]
        exact Or.inr rfl
    have hr : τ (rightLayer v) = υ (rightLayer v) := by
      rcases internalEnds_cases hv with hleft | hright
      · apply hadj
        rw [← hleft]
        exact adjacent_left_right v
      · simpa [hright] using hsame
    rw [hl, hr]
  · simp [hv]

/-- Flipping other V positions cannot change an unflipped V layer's NN ends. -/
lemma nnInternalEnds_flip_subset {k : ℕ} (hk : 0 < k) (s : ℕ)
    (τ : Fin (2 * k + s) → Bool) (S : Finset (Fin (2 * k + s)))
    (hS : S ⊆ vLayers hk s) {i : Fin (2 * k + s)}
    (hi : i ∈ vLayers hk s) (hiS : i ∉ S) :
    nnInternalEnds (fun j => if j ∈ S then true else τ j) i = nnInternalEnds τ i := by
  apply nnInternalEnds_congr
  · simp [hiS]
  · intro j hij
    have hj : j ∉ S := fun hjS => vLayers_independent hk s hi hij (hS hjS)
    simp [hj]

end Problem335.BalancedSchedule

end

end OAI
