import OAI.Combinatorics.MatrixRemoval.HostModeIncidence

namespace OAI

/-!
Sparsity for arbitrary selected raw host positions.
Only the selected core is assumed to consist of anchors; outside it the
selection may include variable and dummy positions.
-/
universe uI

noncomputable section
namespace Problem348.Construction.SelectedAnchors

/-- Anchor mode and group, forgetting the irrelevant within-group offset. -/
def label {h : ℕ} : Position h → Option (Mode h × Fin 64)
  | .inl a => some (a.1, a.2.1)
  | .inr _ => none

/-- The mode classifier used by the abstract rigidity theorem. -/
def mode {h : ℕ} : Position h → Option (Mode h)
  | .inl a => some a.1
  | .inr _ => none

/-- Group uniqueness only concerns anchors, so it permits many nonanchors. -/
def GroupInjective {I : Type uI} {h : ℕ} (f : I → Position h) : Prop :=
  ∀ i j a b, f i = .inl a → f j = .inl b →
    a.1 = b.1 → a.2.1 = b.2.1 → i = j

/-- Restrict the actual sparse-row theorem to an arbitrary selected anchor core. -/
theorem variable_row_core_card_le_four {I : Type uI} [DecidableEq I] {h : ℕ}
    (f : I → Position h) (S : Finset I) (v : VariablePosition h)
    (hanchor : ∀ i ∈ S, ∃ a, f i = .inl a)
    (hgroups : Set.InjOn (fun i => label (f i)) (S : Set I)) :
    (S.filter (fun i => host (.inr (.inl v)) (f i) = true)).card ≤ 4 := by
  classical
  let a : S → AnchorPosition h := fun i => Classical.choose (hanchor i i.property)
  have ha (i : S) : f i = .inl (a i) := Classical.choose_spec (hanchor i i.property)
  have hg : Set.InjOn (fun i : S => ((a i).1, (a i).2.1)) S.attach := by
    intro i hi j hj hij
    apply Subtype.ext
    apply hgroups i.property j.property
    simp only [ha, label]
    exact congrArg some hij
  have hb := card_variable_row_anchor_ones_le_four v S.attach a hg
  simp only [← ha] at hb
  have he := congrArg Finset.card
    (Finset.filter_attach (fun i : I => host (.inr (.inl v)) (f i) = true) S)
  simp only [Finset.card_map, Finset.card_attach] at he
  exact he ▸ hb

/-- The transpose restriction to a selected anchor core. -/
theorem variable_col_core_card_le_four {I : Type uI} [DecidableEq I] {h : ℕ}
    (f : I → Position h) (S : Finset I) (v : VariablePosition h)
    (hanchor : ∀ i ∈ S, ∃ a, f i = .inl a)
    (hgroups : Set.InjOn (fun i => label (f i)) (S : Set I)) :
    (S.filter (fun i => host (f i) (.inr (.inl v)) = true)).card ≤ 4 := by
  classical
  let a : S → AnchorPosition h := fun i => Classical.choose (hanchor i i.property)
  have ha (i : S) : f i = .inl (a i) := Classical.choose_spec (hanchor i i.property)
  have hg : Set.InjOn (fun i : S => ((a i).1, (a i).2.1)) S.attach := by
    intro i hi j hj hij
    apply Subtype.ext
    apply hgroups i.property j.property
    simp only [ha, label]
    exact congrArg some hij
  have hb := card_variable_col_anchor_ones_le_four v S.attach a hg
  simp only [← ha] at hb
  have he := congrArg Finset.card
    (Finset.filter_attach (fun i : I => host (f i) (.inr (.inl v)) = true) S)
  simp only [Finset.card_map, Finset.card_attach] at he
  exact he ▸ hb

/-- The structural group-uniqueness property gives label injectivity on a core. -/
theorem GroupInjective.injOn {I : Type uI} {h : ℕ} {f : I → Position h}
    (hf : GroupInjective f) (S : Set I)
    (hanchor : ∀ i ∈ S, ∃ a, f i = .inl a) :
    Set.InjOn (fun i => label (f i)) S := by
  intro i hi j hj hij
  obtain ⟨a, ha⟩ := hanchor i hi
  obtain ⟨b, hb⟩ := hanchor j hj
  have hab : (a.1, a.2.1) = (b.1, b.2.1) := by
    simpa only [ha, hb, label, Option.some.injEq] using hij
  exact hf i j a b ha hb (congrArg (fun x : Mode h × Fin 64 => x.1) hab)
    (congrArg (fun x : Mode h × Fin 64 => x.2) hab)

/-- Exact nonanchor-row unit hypothesis of the abstract rigidity theorem. -/
theorem nonanchor_row_unit {I : Type uI} {h : ℕ}
    (f : I → Position h) (hf : GroupInjective f)
    (r : VariablePosition h ⊕ Fin (2 ^ h)) (i j : I) (t : Mode h)
    (hi : mode (f i) = some t) (hj : mode (f j) = some t)
    (hri : host (.inr r) (f i) = true)
    (hrj : host (.inr r) (f j) = true) : i = j := by
  cases hfi : f i with
  | inr x => simp [hfi, mode] at hi
  | inl a =>
    cases hfj : f j with
    | inr x => simp [hfj, mode] at hj
    | inl b =>
      have hm : a.1 = b.1 := by simpa [hfi, hfj, mode] using hi.trans hj.symm
      have hg : a.2.1 = b.2.1 := row_anchor_ones_unique_group r a b
        (by simpa [hfi] using hri) (by simpa [hfj] using hrj) hm
      exact hf i j a b hfi hfj hm hg

/-- Exact nonanchor-column unit hypothesis of the abstract rigidity theorem. -/
theorem nonanchor_col_unit {I : Type uI} {h : ℕ}
    (f : I → Position h) (hf : GroupInjective f)
    (c : VariablePosition h ⊕ Fin (2 ^ h)) (i j : I) (t : Mode h)
    (hi : mode (f i) = some t) (hj : mode (f j) = some t)
    (hci : host (f i) (.inr c) = true)
    (hcj : host (f j) (.inr c) = true) : i = j := by
  cases hfi : f i with
  | inr x => simp [hfi, mode] at hi
  | inl a =>
    cases hfj : f j with
    | inr x => simp [hfj, mode] at hj
    | inl b =>
      have hm : a.1 = b.1 := by simpa [hfi, hfj, mode] using hi.trans hj.symm
      have hg : a.2.1 = b.2.1 := col_anchor_ones_unique_group c a b
        (by simpa [hfi] using hci) (by simpa [hfj] using hcj) hm
      exact hf i j a b hfi hfj hm hg

/-- The raw dummy-position predicate. -/
def IsDummy {h : ℕ} (p : Position h) : Prop :=
  ∃ d, p = .inr (.inr d)

/-- A mode-free non-dummy position is a variable position. -/
theorem variable_of_mode_none_not_dummy {h : ℕ} (p : Position h)
    (hm : mode p = none) (hd : ¬ IsDummy p) :
    ∃ v, p = .inr (.inl v) := by
  rcases p with a | (v | d)
  · simp [mode] at hm
  · exact ⟨v, rfl⟩
  · exact False.elim (hd ⟨d, rfl⟩)

/-- The exact variable-column sparsity input of one-sided anchor rigidity. -/
theorem sparse_column_of_mode_none {I : Type uI} [DecidableEq I] {h : ℕ}
    (f : I → Position h) (S : Finset I) (p : Position h)
    (hanchor : ∀ i ∈ S, ∃ a, f i = .inl a)
    (hgroups : GroupInjective f)
    (hm : mode p = none) (hd : ¬ IsDummy p) :
    (S.filter (fun i => host (f i) p = true)).card ≤ 4 := by
  obtain ⟨v, rfl⟩ := variable_of_mode_none_not_dummy p hm hd
  exact variable_col_core_card_le_four f S v hanchor
    (hgroups.injOn S hanchor)

/-- The axis-transposed sparsity input. -/
theorem sparse_row_of_mode_none {I : Type uI} [DecidableEq I] {h : ℕ}
    (f : I → Position h) (S : Finset I) (p : Position h)
    (hanchor : ∀ i ∈ S, ∃ a, f i = .inl a)
    (hgroups : GroupInjective f)
    (hm : mode p = none) (hd : ¬ IsDummy p) :
    (S.filter (fun i => host p (f i) = true)).card ≤ 4 := by
  obtain ⟨v, rfl⟩ := variable_of_mode_none_not_dummy p hm hd
  exact variable_row_core_card_le_four f S v hanchor
    (hgroups.injOn S hanchor)

/-- An anchor-anchor one forces equality of the two mode labels. -/
theorem cross_mode {h : ℕ} (r c : Position h) (t u : Mode h)
    (hr : mode r = some t) (hc : mode c = some u)
    (hentry : host r c = true) : t = u := by
  rcases r with a | r
  · rcases c with b | c
    · have hat : a.1 = t := by simpa [mode] using hr
      have hbu : b.1 = u := by simpa [mode] using hc
      by_contra htu
      have hab : a.1 ≠ b.1 := by simpa [hat, hbu] using htu
      simp [host, hab] at hentry
    · simp [mode] at hc
  · simp [mode] at hr

/-- Raw-position form matching the abstract nonanchor-row unit hypothesis. -/
theorem nonanchor_row_unit_of_mode_none {I : Type uI} {h : ℕ}
    (f : I → Position h) (hf : GroupInjective f) (r : Position h)
    (hr : mode r = none) (i j : I) (t : Mode h)
    (hi : mode (f i) = some t) (hj : mode (f j) = some t)
    (hri : host r (f i) = true) (hrj : host r (f j) = true) : i = j := by
  rcases r with a | r
  · simp [mode] at hr
  · exact nonanchor_row_unit f hf r i j t hi hj hri hrj

/-- Raw-position form matching the abstract nonanchor-column unit hypothesis. -/
theorem nonanchor_col_unit_of_mode_none {I : Type uI} {h : ℕ}
    (f : I → Position h) (hf : GroupInjective f) (c : Position h)
    (hc : mode c = none) (i j : I) (t : Mode h)
    (hi : mode (f i) = some t) (hj : mode (f j) = some t)
    (hci : host (f i) c = true) (hcj : host (f j) c = true) : i = j := by
  rcases c with a | c
  · simp [mode] at hc
  · exact nonanchor_col_unit f hf c i j t hi hj hci hcj

end Problem348.Construction.SelectedAnchors

end

end OAI
