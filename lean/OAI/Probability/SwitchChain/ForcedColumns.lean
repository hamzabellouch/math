import OAI.Probability.SwitchChain.BinaryColumnPartitions

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.ForcedColumns

variable {C : Type*}

abbrev MatrixSpace (k : C → ℕ) :=
  {M : Fin 3 → C → Fin 2 // ∀ c, ∑ i, (M i c : ℕ) = k c}

abbrev One (k : C → ℕ) := {c : C // k c = 1}
abbrev Two (k : C → ℕ) := {c : C // k c = 2}

lemma column_zero (v : Fin 3 → Fin 2) (h : ∑ i, (v i : ℕ) = 0) :
    ∀ i, v i = 0 := by
  have ht : ∀ v : Fin 3 → Fin 2, (∑ i, (v i : ℕ)) = 0 → ∀ i, v i = 0 := by decide
  exact ht v h

lemma column_three (v : Fin 3 → Fin 2) (h : ∑ i, (v i : ℕ) = 3) :
    ∀ i, v i = 1 := by
  have ht : ∀ v : Fin 3 → Fin 2, (∑ i, (v i : ℕ)) = 3 → ∀ i, v i = 1 := by decide
  exact ht v h

def restrict (k : C → ℕ) (M : MatrixSpace k) :
    BinaryColumnPartitions.MatrixSpace (One k) (Two k) :=
  ⟨fun i => Sum.elim (fun c => M.val i c.val) (fun c => M.val i c.val),
    ⟨fun c => (M.property c.val).trans c.property,
     fun c => (M.property c.val).trans c.property⟩⟩

def extend (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : BinaryColumnPartitions.MatrixSpace (One k) (Two k)) : MatrixSpace k := by
  classical
  refine ⟨fun i c => if h1 : k c = 1 then M.val i (Sum.inl ⟨c, h1⟩)
    else if h2 : k c = 2 then M.val i (Sum.inr ⟨c, h2⟩)
    else if k c = 3 then 1 else 0, ?_⟩
  intro c
  by_cases h1 : k c = 1
  · simpa [h1] using M.property.1 ⟨c, h1⟩
  · by_cases h2 : k c = 2
    · simpa [h2] using M.property.2 ⟨c, h2⟩
    · by_cases h3 : k c = 3
      · simp [h3]
      · have h0 : k c = 0 := by have := hk c; omega
        simp [h0]

@[simp] theorem restrict_extend (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : BinaryColumnPartitions.MatrixSpace (One k) (Two k)) :
    restrict k (extend k hk M) = M := by
  classical
  apply Subtype.ext
  funext i c
  cases c with
  | inl c => simp [restrict, extend, c.property]
  | inr c => simp [restrict, extend, c.property]

@[simp] theorem extend_restrict (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : MatrixSpace k) : extend k hk (restrict k M) = M := by
  classical
  apply Subtype.ext
  funext i c
  by_cases h1 : k c = 1
  · simp [extend, restrict, h1]
  · by_cases h2 : k c = 2
    · simp [extend, restrict, h2]
    · by_cases h3 : k c = 3
      · have he : M.val i c = 1 := column_three (fun j => M.val j c)
          ((M.property c).trans h3) i
        simp [extend, h3, he]
      · have h0 : k c = 0 := by have := hk c; omega
        have he : M.val i c = 0 := column_zero (fun j => M.val j c)
          ((M.property c).trans h0) i
        simp [extend, h0, he]

def matrixEquiv (k : C → ℕ) (hk : ∀ c, k c ≤ 3) :
    MatrixSpace k ≃ BinaryColumnPartitions.MatrixSpace (One k) (Two k) where
  toFun := restrict k
  invFun := extend k hk
  left_inv := extend_restrict k hk
  right_inv := restrict_extend k hk

theorem row_eq_iff (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M N : MatrixSpace k) (i : Fin 3) :
    (restrict k M).val i = (restrict k N).val i ↔ M.val i = N.val i := by
  constructor
  · intro h
    funext c
    by_cases h1 : k c = 1
    · exact congrFun h (Sum.inl ⟨c, h1⟩)
    · by_cases h2 : k c = 2
      · exact congrFun h (Sum.inr ⟨c, h2⟩)
      · by_cases h3 : k c = 3
        · exact (column_three _ ((M.property c).trans h3) i).trans
            (column_three _ ((N.property c).trans h3) i).symm
        · have h0 : k c = 0 := by have := hk c; omega
          exact (column_zero _ ((M.property c).trans h0) i).trans
            (column_zero _ ((N.property c).trans h0) i).symm
  · intro h
    funext c
    cases c with
    | inl c => exact congrFun h c.val
    | inr c => exact congrFun h c.val

attribute [local instance] Classical.propDecidable
variable [Fintype C]

def offset (k : C → ℕ) : ℕ := Fintype.card {c : C // k c = 3}

theorem row_sum (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : MatrixSpace k) (i : Fin 3) :
    (∑ c, (M.val i c : ℕ)) =
      (∑ c, ((restrict k M).val i c : ℕ)) + offset k := by
  classical
  have hs (a : ℕ) : (∑ c : {c : C // k c = a}, (M.val i c.val : ℕ)) =
      ∑ c : C, if k c = a then (M.val i c : ℕ) else 0 := by
    symm
    simpa only [Finset.sum_filter] using
      (Finset.sum_subtype (Finset.univ.filter (fun c => k c = a))
        (by intro c; simp) (fun c => (M.val i c : ℕ)))
  have hp (c : C) : (M.val i c : ℕ) =
      (if k c = 1 then (M.val i c : ℕ) else 0) +
      (if k c = 2 then (M.val i c : ℕ) else 0) +
      (if k c = 3 then 1 else 0) := by
    have hc : k c = 0 ∨ k c = 1 ∨ k c = 2 ∨ k c = 3 := by
      have := hk c
      omega
    rcases hc with h | h | h | h
    · have he := column_zero _ ((M.property c).trans h) i
      simp [h, he]
    · simp [h]
    · simp [h]
    · have he := column_three _ ((M.property c).trans h) i
      simp [h, he]
  have ht := congrArg (fun f : C → ℕ => ∑ c, f c) (funext hp)
  simp only [Finset.sum_add_distrib] at ht
  rw [Fintype.sum_sum_type]
  change (∑ c, (M.val i c : ℕ)) =
    ((∑ c : One k, (M.val i c.val : ℕ)) +
      ∑ c : Two k, (M.val i c.val : ℕ)) + offset k
  rw [hs 1, hs 2]
  have ho : (∑ c : C, if k c = 3 then 1 else 0) = offset k := by
    simp [offset, Fintype.card_subtype]
  simpa only [ho] using ht

theorem offset_le_row_sum (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : MatrixSpace k) (i : Fin 3) : offset k ≤ ∑ c, (M.val i c : ℕ) := by
  rw [row_sum k hk M i]
  omega

def fixedMarginsEquiv (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (r : Fin 3 → ℕ) (hr : ∀ i, offset k ≤ r i) :
    {M : MatrixSpace k // ∀ i, ∑ c, (M.val i c : ℕ) = r i} ≃
      {M : BinaryColumnPartitions.MatrixSpace (One k) (Two k) //
        ∀ i, ∑ c, (M.val i c : ℕ) = r i - offset k} :=
  (matrixEquiv k hk).subtypeEquiv (fun M => by
    constructor
    · intro h i
      have hh := row_sum k hk M i
      have hi := h i
      change (∑ c, ((restrict k M).val i c : ℕ)) = r i - offset k
      omega
    · intro h i
      have hh := row_sum k hk M i
      have hi := h i
      have hle := hr i
      change (∑ c, ((restrict k M).val i c : ℕ)) = r i - offset k at hi
      omega)

abbrev FullMargins (k : C → ℕ) (r : Fin 3 → ℕ) :=
  {M : Fin 3 → C → Fin 2 //
    (∀ i, ∑ c, (M i c : ℕ) = r i) ∧ ∀ c, ∑ i, (M i c : ℕ) = k c}

def nestEquiv (k : C → ℕ) (r : Fin 3 → ℕ) :
    FullMargins k r ≃ {M : MatrixSpace k // ∀ i, ∑ c, (M.val i c : ℕ) = r i} where
  toFun M := ⟨⟨M.val, M.property.2⟩, M.property.1⟩
  invFun M := ⟨M.val.val, M.property, M.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem bounds_of_nonempty (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (FullMargins k r)) :
    (∀ c, k c ≤ 3) ∧ ∀ i, offset k ≤ r i := by
  obtain ⟨M⟩ := h
  have hk (c : C) : k c ≤ 3 := by
    rw [← M.property.2 c]
    calc
      (∑ i, (M.val i c : ℕ)) ≤ ∑ _i : Fin 3, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        have := (M.val i c).isLt
        omega
      _ = 3 := by simp
  refine ⟨hk, ?_⟩
  intro i
  have hi := offset_le_row_sum k hk ⟨M.val, M.property.2⟩ i
  simpa only [M.property.1 i] using hi

abbrev Colorings (k : C → ℕ) (r : Fin 3 → ℕ) :=
  {c : (One k → Fin 3) × (Two k → Fin 3) // ∀ i,
    (FixedBlock.row c.1 i).card + Fintype.card (Two k) =
      (r i - offset k) + (FixedBlock.row c.2 i).card}

def coloringEquiv (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (FullMargins k r)) : FullMargins k r ≃ Colorings k r :=
  (nestEquiv k r).trans
    ((fixedMarginsEquiv k (bounds_of_nonempty k r h).1 r
      (bounds_of_nonempty k r h).2).trans
      (BinaryColumnPartitions.fixedMarginsEquiv (One k) (Two k)
        (fun i => r i - offset k)).symm)

theorem coloring_row_eq_iff (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (FullMargins k r)) (M N : FullMargins k r) (i : Fin 3) :
    M.val i = N.val i ↔
      FixedBlock.row (coloringEquiv k r h M).val.1 i =
        FixedBlock.row (coloringEquiv k r h N).val.1 i ∧
      FixedBlock.row (coloringEquiv k r h M).val.2 i =
        FixedBlock.row (coloringEquiv k r h N).val.2 i := by
  let m : MatrixSpace k := ⟨M.val, M.property.2⟩
  let n : MatrixSpace k := ⟨N.val, N.property.2⟩
  have hm : BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      (coloringEquiv k r h M).val = restrict k m := by
    change BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      ((BinaryColumnPartitions.matrixEquiv (One k) (Two k)).symm (restrict k m)) = _
    exact Equiv.apply_symm_apply _ _
  have hn : BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      (coloringEquiv k r h N).val = restrict k n := by
    change BinaryColumnPartitions.matrixEquiv (One k) (Two k)
      ((BinaryColumnPartitions.matrixEquiv (One k) (Two k)).symm (restrict k n)) = _
    exact Equiv.apply_symm_apply _ _
  have hb := BinaryColumnPartitions.row_eq_iff (One k) (Two k)
    (coloringEquiv k r h M).val (coloringEquiv k r h N).val i
  rw [hm, hn] at hb
  exact (row_eq_iff k (bounds_of_nonempty k r h).1 m n i).symm.trans hb

end Problem315.ForcedColumns

end

end OAI
