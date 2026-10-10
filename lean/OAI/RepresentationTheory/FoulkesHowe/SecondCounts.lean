import OAI.RepresentationTheory.FoulkesHowe.SecondLabels

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SecondTransfer

/-- A source occurrence lies in exactly one nonzero row and beyond its
already-transferred prefix. -/
theorem label_eq_source_iff {r b : ℕ} (k : Fin r → ℕ)
    (i : Fin r) (p : Fin (r+1) × Fin b) :
    label k p = some i.succ ↔ p.1 = i.succ ∧ k i ≤ p.2.val := by
  rcases p with ⟨l,j⟩
  refine Fin.cases ?_ (fun l => ?_) l
  · simp [Ne.symm (Fin.succ_ne_zero i)]
  · by_cases h : l = i
    · subst l
      simp [not_lt]
    · simp [label_succ_row, Fin.succ_inj, h]

private theorem sum_fin_ite_lt (b k : ℕ) (hk : k ≤ b) :
    (∑ j : Fin b, if j.val < k then 1 else 0) = k := by
  classical
  by_cases h : k < b
  · let c : Fin b := ⟨k,h⟩
    have hs : Finset.univ.filter (fun j : Fin b => j.val < k) = Finset.Iio c := by
      ext j
      simp [c, Fin.lt_def]
    rw [← Finset.card_filter, hs, Fin.card_Iio]
  · have hkb : k = b := by omega
    subst k
    simp

private theorem sum_fin_ite_le (b k : ℕ) (hk : k ≤ b) :
    (∑ j : Fin b, if k ≤ j.val then 1 else 0) = b-k := by
  classical
  have h := sum_fin_ite_lt b k hk
  have hs : (∑ j : Fin b, if j.val < k then 1 else 0) +
      (∑ j : Fin b, if k ≤ j.val then 1 else 0) = b := by
    rw [← Finset.sum_add_distrib]
    have : ∀ j : Fin b, (if j.val < k then 1 else 0) +
        (if k ≤ j.val then 1 else 0) = (1 : ℕ) := by
      intro j
      split_ifs <;> omega
    simp_rw [this]
    simp
  omega

/-- Number of occurrences of the still-independent vector in row `i`. -/
theorem source_occurrences {r b : ℕ} (k : Fin r → ℕ)
    (hk : ∀ i, k i ≤ b) (i : Fin r) :
    (∑ p : Fin (r+1) × Fin b, if label k p = some i.succ then 1 else 0) = b-k i := by
  classical
  simp_rw [label_eq_source_iff]
  rw [Fintype.sum_prod_type]
  dsimp only
  simp only [ite_and]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j : Fin b, if k i ≤ j.val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_eq_single i.succ]
      · simp
      · intro l hl hli
        simp [hli]
      · simp
    _ = b-k i := sum_fin_ite_le b (k i) (hk i)

/-- Number of occurrences of the shared destination vector. -/
theorem destination_occurrences {r b : ℕ} (k : Fin r → ℕ)
    (hk : ∀ i, k i ≤ b) :
    (∑ p : Fin (r+1) × Fin b, if label k p = none then 1 else 0) = ∑ i, k i := by
  classical
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [label_zero_row, reduceCtorEq, ite_false, Finset.sum_const_zero, zero_add,
    label_succ_row]
  apply Finset.sum_congr rfl
  intro i hi
  convert sum_fin_ite_lt b (k i) (hk i) using 1
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp_all

/-- Cardinality version of the source occurrence formula. -/
theorem source_card {r b : ℕ} (k : Fin r → ℕ)
    (hk : ∀ i, k i ≤ b) (i : Fin r) :
    (Finset.univ.filter (fun p : Fin (r+1) × Fin b => label k p = some i.succ)).card =
      b-k i := by
  classical
  rw [Finset.card_filter]
  exact source_occurrences k hk i

/-- Cardinality version of the destination occurrence formula. -/
theorem destination_card {r b : ℕ} (k : Fin r → ℕ)
    (hk : ∀ i, k i ≤ b) :
    (Finset.univ.filter (fun p : Fin (r+1) × Fin b => label k p = none)).card =
      ∑ i, k i := by
  classical
  rw [Finset.card_filter]
  exact destination_occurrences k hk

/-- At every unfinished row, the quadratic threshold makes the source degree
strictly larger than the accumulated shared-destination degree. -/
theorem source_degree_gt_destination {r b : ℕ} (k : Fin r → ℕ)
    (hb : r * (r+1) ≤ b) (hk : ∀ j, k j ≤ r)
    (i : Fin r) (hi : k i < r) :
    (∑ j, k j) < b - k i := by
  have hsum : (∑ j, k j) ≤ r*r := by
    calc
      _ ≤ ∑ _ : Fin r, r := Finset.sum_le_sum (fun j _ => hk j)
      _ = r*r := by simp
  have hquad : r*r+r ≤ b := by nlinarith
  omega

/-- The actual occurrence counts satisfy the positive-weight hypothesis
used to cancel a shift at any unfinished row. -/
theorem destination_occurrences_lt_source {r b : ℕ} (k : Fin r → ℕ)
    (hb : r * (r+1) ≤ b) (hk : ∀ j, k j ≤ r)
    (i : Fin r) (hi : k i < r) :
    (∑ p : Fin (r+1) × Fin b, if label k p = none then 1 else 0) <
      ∑ p : Fin (r+1) × Fin b, if label k p = some i.succ then 1 else 0 := by
  have hrb : r ≤ b := by nlinarith
  have hkb : ∀ j, k j ≤ b := fun j => (hk j).trans hrb
  rw [destination_occurrences k hkb, source_occurrences k hkb]
  exact source_degree_gt_destination k hb hk i hi

end Problem346.SecondTransfer

end

end OAI
