import Mathlib

namespace OAI

/-!
Finite combinatorial anchor rigidity under explicit density, sparsity,
and mode-incidence hypotheses.
-/

universe uI uJ uT

namespace Problem348.AnchorRigidity

/-- At most one zero leaves all but at most one position equal to one. -/
theorem card_le_true_card_add_one {I : Type uI} [DecidableEq I]
    (s : Finset I) (f : I → Bool)
    (hz : (s.filter fun i => f i = false).card ≤ 1) :
    s.card ≤ (s.filter fun i => f i = true).card + 1 := by
  classical
  have hp := Finset.card_filter_add_card_filter_not (s := s)
    (p := fun i => f i = true)
  have hn : (s.filter fun i => ¬ f i = true).card ≤ 1 := by
    simpa only [Bool.not_eq_true] using hz
  omega

/-- Two columns with at most one zero share a one on any core of size at least three. -/
theorem exists_common_true {I : Type uI} [DecidableEq I]
    (s : Finset I) (f g : I → Bool) (hs : 3 ≤ s.card)
    (hf : (s.filter fun i => f i = false).card ≤ 1)
    (hg : (s.filter fun i => g i = false).card ≤ 1) :
    ∃ i ∈ s, f i = true ∧ g i = true := by
  classical
  by_contra h
  have hsub : (s.filter fun i => f i = true) ⊆
      (s.filter fun i => g i = false) := by
    intro i hi
    obtain ⟨his, hif⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨his, ?_⟩
    cases hgi : g i with
    | false => rfl
    | true => exact False.elim (h ⟨i, his, hif, hgi⟩)
  have hcard := Finset.card_le_card hsub
  have hpos := card_le_true_card_add_one s f hf
  omega

/-- One-sided rigidity.  A dense anchor core on the row axis forces both axes
into one mode.  The dummy predicate is only needed to permit one exceptional
non-anchor column before the common mode has been identified. -/
theorem one_sided
    {I : Type uI} {J : Type uJ} {T : Type uT} [Fintype I] [Fintype J]
    (B : I → J → Bool) (rowMode : I → Option T) (colMode : J → Option T)
    (dummyCol : J → Prop) (core : Finset I)
    (hcore : 6 ≤ core.card)
    (core_anchor : ∀ i ∈ core, ∃ t, rowMode i = some t)
    (core_zeros : ∀ j, (core.filter fun i => B i j = false).card ≤ 1)
    (variable_sparse : ∀ j, colMode j = none → ¬ dummyCol j →
      (core.filter fun i => B i j = true).card ≤ 4)
    (dummy_unique : ∀ j k, dummyCol j → dummyCol k → j = k)
    (cross_mode : ∀ i j t u, rowMode i = some t → colMode j = some u →
      B i j = true → t = u)
    (nonanchor_row_unit : ∀ i, rowMode i = none → ∀ j k t,
      colMode j = some t → colMode k = some t →
      B i j = true → B i k = true → j = k)
    (nonanchor_col_unit : ∀ j, colMode j = none → ∀ i k t,
      rowMode i = some t → rowMode k = some t →
      B i j = true → B k j = true → i = k)
    (row_dense : ∀ i, 2 ≤ (Finset.univ.filter fun j => B i j = true).card) :
    ∃ t, (∀ i, rowMode i = some t) ∧ (∀ j, colMode j = some t) := by
  classical
  have core_positive (j : J) : 5 ≤ (core.filter fun i => B i j = true).card := by
    have h := card_le_true_card_add_one core (fun i => B i j) (core_zeros j)
    omega
  have nonanchor_dummy (j : J) (hj : colMode j = none) : dummyCol j := by
    by_contra hd
    have hs := variable_sparse j hj hd
    have hp := core_positive j
    omega
  have nonanchor_unique (j k : J) (hj : colMode j = none)
      (hk : colMode k = none) : j = k :=
    dummy_unique j k (nonanchor_dummy j hj) (nonanchor_dummy k hk)
  have two_ones (i : I) : ∃ j k, B i j = true ∧ B i k = true ∧ j ≠ k := by
    have hd := row_dense i
    obtain ⟨j, hj, k, hk, hne⟩ := Finset.one_lt_card.mp (show
      1 < (Finset.univ.filter fun j => B i j = true).card by omega)
    exact ⟨j, k, (Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hk).2, hne⟩
  have row_anchor_one (i : I) : ∃ j t, colMode j = some t ∧ B i j = true := by
    obtain ⟨j, k, hj, hk, hne⟩ := two_ones i
    cases hmj : colMode j with
    | some t => exact ⟨j, t, hmj, hj⟩
    | none =>
      cases hmk : colMode k with
      | some t => exact ⟨k, t, hmk, hk⟩
      | none => exact False.elim (hne (nonanchor_unique j k hmj hmk))
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (show 0 < core.card by omega)
  obtain ⟨j₀, t, hj₀, _⟩ := row_anchor_one i₀
  have anchor_columns (j : J) (u : T) (hj : colMode j = some u) : u = t := by
    obtain ⟨i, hi, hij, hij₀⟩ := exists_common_true core
      (fun i => B i j) (fun i => B i j₀) (by omega) (core_zeros j) (core_zeros j₀)
    obtain ⟨v, hiv⟩ := core_anchor i hi
    exact (cross_mode i j v u hiv hj hij).symm.trans
      (cross_mode i j₀ v t hiv hj₀ hij₀)
  have anchor_rows (i : I) (u : T) (hi : rowMode i = some u) : u = t := by
    obtain ⟨j, v, hj, hij⟩ := row_anchor_one i
    exact (cross_mode i j u v hi hj hij).trans (anchor_columns j v hj)
  have core_same (i : I) (hi : i ∈ core) : rowMode i = some t := by
    obtain ⟨u, hu⟩ := core_anchor i hi
    simpa only [anchor_rows i u hu] using hu
  have all_columns (j : J) : colMode j = some t := by
    cases hj : colMode j with
    | some u => simp only [anchor_columns j u hj]
    | none =>
      have hs : (core.filter fun i => B i j = true).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro i hi k hk
        obtain ⟨hic, hij⟩ := Finset.mem_filter.mp hi
        obtain ⟨hkc, hkj⟩ := Finset.mem_filter.mp hk
        exact nonanchor_col_unit j hj i k t (core_same i hic) (core_same k hkc) hij hkj
      have hp := core_positive j
      omega
  refine ⟨t, ?_, all_columns⟩
  intro i
  cases hi : rowMode i with
  | some u => simp only [anchor_rows i u hi]
  | none =>
    obtain ⟨j, k, hj, hk, hne⟩ := two_ones i
    exact False.elim (hne (nonanchor_row_unit i hi j k t
      (all_columns j) (all_columns k) hj hk))

/-- A dense core consists of at least six selected anchor positions.  Every
opposite position has at most one zero on it, while a variable opposite
position would have at most four ones. -/
def DenseAnchorCore {I : Type uI} {J : Type uJ} {T : Type uT}
    (B : I → J → Bool) (rowMode : I → Option T) (colMode : J → Option T)
    (dummyCol : J → Prop) : Prop :=
  ∃ core : Finset I, 6 ≤ core.card ∧
    (∀ i ∈ core, ∃ t, rowMode i = some t) ∧
    (∀ j, (core.filter fun i => B i j = false).card ≤ 1) ∧
    (∀ j, colMode j = none → ¬ dummyCol j →
      (core.filter fun i => B i j = true).card ≤ 4)

/-- Symmetric form of anchor rigidity: a dense anchor core on either axis
suffices.  The no-shattering/order argument supplies this disjunction in the
application to the 64 by 64 pattern. -/
theorem rigidity
    {I : Type uI} {J : Type uJ} {T : Type uT} [Fintype I] [Fintype J]
    (B : I → J → Bool) (rowMode : I → Option T) (colMode : J → Option T)
    (dummyRow : I → Prop) (dummyCol : J → Prop)
    (hcore : DenseAnchorCore B rowMode colMode dummyCol ∨
      DenseAnchorCore (fun j i => B i j) colMode rowMode dummyRow)
    (dummy_row_unique : ∀ i k, dummyRow i → dummyRow k → i = k)
    (dummy_col_unique : ∀ j k, dummyCol j → dummyCol k → j = k)
    (cross_mode : ∀ i j t u, rowMode i = some t → colMode j = some u →
      B i j = true → t = u)
    (nonanchor_row_unit : ∀ i, rowMode i = none → ∀ j k t,
      colMode j = some t → colMode k = some t →
      B i j = true → B i k = true → j = k)
    (nonanchor_col_unit : ∀ j, colMode j = none → ∀ i k t,
      rowMode i = some t → rowMode k = some t →
      B i j = true → B k j = true → i = k)
    (row_dense : ∀ i, 2 ≤ (Finset.univ.filter fun j => B i j = true).card)
    (col_dense : ∀ j, 2 ≤ (Finset.univ.filter fun i => B i j = true).card) :
    ∃ t, (∀ i, rowMode i = some t) ∧ (∀ j, colMode j = some t) := by
  rcases hcore with hcore | hcore
  · obtain ⟨core, hc, ha, hz, hs⟩ := hcore
    exact one_sided B rowMode colMode dummyCol core hc ha hz hs
      dummy_col_unique cross_mode nonanchor_row_unit nonanchor_col_unit row_dense
  · obtain ⟨core, hc, ha, hz, hs⟩ := hcore
    obtain ⟨t, hcol, hrow⟩ := one_sided (fun j i => B i j) colMode rowMode
      dummyRow core hc ha hz hs dummy_row_unique
      (fun j i u t hj hi hb => (cross_mode i j t u hi hj hb).symm)
      nonanchor_col_unit nonanchor_row_unit col_dense
    exact ⟨t, hrow, hcol⟩

end Problem348.AnchorRigidity

end OAI
