import OAI.RepresentationTheory.FoulkesHowe.FirstLabels

namespace OAI

open scoped BigOperators

namespace Problem346

@[simp] theorem firstLabel_zero (r m k : ℕ) (j : Fin (r + m)) :
    firstLabel r m k (0, j) =
      if h : j.val < k ∧ j.val < m then some (some ⟨j.val, h.2⟩) else some none := by
  simp [firstLabel]

@[simp] theorem firstLabel_succ (r m k : ℕ) (i : Fin r) (j : Fin (r + m)) :
    firstLabel r m k (i.succ, j) =
      Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) j := by
  simp [firstLabel]

@[simp] theorem firstLabel_zero_ne_x (r m k : ℕ) (j : Fin (r + m)) :
    firstLabel r m k (0, j) ≠ none := by
  simp only [firstLabel_zero]
  split <;> simp

theorem firstLabel_zero_eq_t_iff (r m k : ℕ) (hk : k ≤ m) (j : Fin (r + m)) :
    firstLabel r m k (0, j) = some none ↔ k ≤ j.val := by
  simp only [firstLabel_zero]
  split <;> simp_all
  omega

theorem firstLabel_zero_eq_y_iff (r m k : ℕ) (_hk : k ≤ m)
    (j : Fin (r + m)) (y : Fin m) :
    firstLabel r m k (0, j) = some (some y) ↔ j.val = y.val ∧ y.val < k := by
  simp only [firstLabel_zero]
  split
  · simp only [Option.some.injEq, Fin.ext_iff]
    rename_i h
    constructor
    · intro h'
      exact ⟨h', h' ▸ h.1⟩
    · exact fun h' => h'.1
  · rename_i h
    simp only [Option.some.injEq, reduceCtorEq, false_iff]
    omega

/-- Number of individual factors labelled by a given vector block. -/
def firstLabelCount (r m k : ℕ) (c : FirstBlock m) : ℕ :=
  ∑ p : Fin (r + 1) × Fin (r + m), if firstLabel r m k p = c then 1 else 0


theorem firstLabelCount_x (r m k : ℕ) : firstLabelCount r m k none = r * r := by
  classical
  simp only [firstLabelCount, Fintype.sum_prod_type, Fin.sum_univ_succ,
    firstLabel_zero_ne_x, ite_false, Finset.sum_const_zero, zero_add, firstLabel_succ]
  have hrow : (∑ j : Fin (r + m),
      if Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) j =
        (none : FirstBlock m) then 1 else 0) = r := by
    rw [Fin.sum_univ_add]
    simp
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

 theorem firstLabelCount_t (r m k : ℕ) (hk : k ≤ m) :
    firstLabelCount r m k (some none) = r + m - k := by
  classical
  rw [firstLabelCount, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hrow : (∑ j : Fin (r + m),
      if Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) j =
        (some none : FirstBlock m) then 1 else 0) = 0 := by
    rw [Fin.sum_univ_add]
    simp
  simp only [firstLabel_succ, hrow, Finset.sum_const_zero, add_zero,
    firstLabel_zero_eq_t_iff r m k hk]
  rw [← Finset.card_filter]
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (r + m)))) (fun j => j.val < k)
  rw [Fin.card_filter_val_lt, Nat.min_eq_right (by omega)] at hc
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at hc
  omega


theorem firstLabelCount_y (r m k : ℕ) (hk : k ≤ m) (y : Fin m) :
    firstLabelCount r m k (some (some y)) = r + if y.val < k then 1 else 0 := by
  classical
  rw [firstLabelCount, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hrow : (∑ j : Fin (r + m),
      if Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) j =
        (some (some y) : FirstBlock m) then 1 else 0) = 1 := by
    rw [Fin.sum_univ_add]
    simp
  simp only [firstLabel_succ, hrow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  let y' : Fin (r + m) := ⟨y.val, by omega⟩
  have hj : ∀ j : Fin (r + m), j.val = y.val ↔ j = y' := by
    intro j
    change j.val = y'.val ↔ j = y'
    exact Fin.ext_iff.symm
  simp only [firstLabel_zero_eq_y_iff r m k hk, hj]
  by_cases hy : y.val < k <;> simp [hy, add_comm]


theorem firstLabel_step (r m k : ℕ) (hk : k < m) :
    firstLabel r m (k + 1) = Function.update (firstLabel r m k)
      (0, ⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩) (some (some ⟨k, hk⟩)) := by
  classical
  funext p
  rcases p with ⟨i, j⟩
  by_cases hi : i = 0
  · subst i
    by_cases hj : j.val = k
    · have hjeq : j = (⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩ : Fin (r + m)) := Fin.ext hj
      rw [hjeq]
      simp [firstLabel, hk]
    · have hp : ((0 : Fin (r + 1)), j) ≠ (0, (⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩ : Fin (r + m))) := by
        intro h
        exact hj (congrArg (fun p : Fin (r + 1) × Fin (r + m) => p.2.val) h)
      rw [Function.update_of_ne hp]
      have hlt : j.val < k + 1 ↔ j.val < k := by omega
      simp only [firstLabel_zero, hlt]
  · have hp : (i, j) ≠ (0, (⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩ : Fin (r + m))) := by
      intro h
      exact hi (congrArg Prod.fst h)
    rw [Function.update_of_ne hp]
    simp [firstLabel, hi]


/-- The sum-of-indicators count agrees with the cardinality used by polynomial
block-degree statements. -/
theorem firstLabel_card (r m k : ℕ) (c : FirstBlock m) :
    (Finset.univ.filter (fun p => firstLabel r m k p = c)).card =
      firstLabelCount r m k c := by
  classical
  exact Finset.card_filter _ _

theorem firstLabel_card_t (r m k : ℕ) (hk : k ≤ m) :
    (Finset.univ.filter (fun p => firstLabel r m k p = some none)).card = r + m - k := by
  rw [firstLabel_card, firstLabelCount_t r m k hk]

theorem firstLabel_card_y (r m k : ℕ) (hk : k ≤ m) (y : Fin m) :
    (Finset.univ.filter (fun p => firstLabel r m k p = some (some y))).card =
      r + if y.val < k then 1 else 0 := by
  rw [firstLabel_card, firstLabelCount_y r m k hk]

theorem firstLabel_card_y_next (r m k : ℕ) (hk : k < m) :
    (Finset.univ.filter (fun p => firstLabel r m k p = some (some ⟨k, hk⟩))).card = r := by
  rw [firstLabel_card_y r m k (Nat.le_of_lt hk)]
  simp

/-- Only unreplaced positions of the distinguished row carry the source label. -/
theorem firstLabel_eq_t_iff (r m k : ℕ) (hk : k ≤ m)
    (p : Fin (r + 1) × Fin (r + m)) :
    firstLabel r m k p = some none ↔ p.1 = 0 ∧ k ≤ p.2.val := by
  rcases p with ⟨i, j⟩
  by_cases hi : i = 0
  · subst i
    simpa using firstLabel_zero_eq_t_iff r m k hk j
  · simp only [firstLabel, hi, ite_false, false_and, iff_false]
    refine Fin.addCases (fun x => ?_) (fun y => ?_) j <;> simp

end Problem346

end OAI
