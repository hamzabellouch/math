import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.AnchorRigidityFixed
import OAI.Combinatorics.MatrixRemoval.HostTwins
import OAI.Combinatorics.MatrixRemoval.AnchorProperties
import OAI.Combinatorics.MatrixRemoval.AnchorRigidity

namespace OAI


/-! Concrete cross-mode and single-mode incidence facts for the canonical host.
These discharge the corresponding premises of abstract anchor rigidity once
an anchor copy has distinct selected anchor groups. -/
universe uI uJ

namespace Problem348.AnchorRigidity

open Construction

/-- The mode label of a raw anchor position, and `none` off the anchors. -/
def positionMode {h : ℕ} : Position h → Option (Mode h)
  | Sum.inl (t, _, _) => some t
  | Sum.inr _ => none

/-- Group label, ignoring the within-group coordinate. -/
def positionGroup {h : ℕ} : Position h → Option (Mode h × Fin 64)
  | Sum.inl (t, u, _) => some (t, u)
  | Sum.inr _ => none

/-- A selected family uses each anchor group at most once. -/
def DistinctAnchorGroups {h : ℕ} {I : Type uI} (r : I → Position h) : Prop :=
  ∀ i j g, positionGroup (r i) = some g → positionGroup (r j) = some g → i = j

/-- A true entry between anchors forces their modes to agree. -/
theorem host_cross_mode {h : ℕ} (r c : Position h) (t u : Mode h)
    (hr : positionMode r = some t) (hc : positionMode c = some u)
    (hb : host r c = true) : t = u := by
  rcases r with ⟨tr, ur, xr⟩ | r
  · rcases c with ⟨tc, vc, yc⟩ | c
    · simp only [positionMode, Option.some.injEq] at hr hc
      subst tr
      subst tc
      by_contra hne
      simp [host, hne] at hb
    · simp [positionMode] at hc
  · simp [positionMode] at hr

/-- On the columns of one mode, a nonanchor row has ones in only one group. -/
theorem host_nonanchor_row_one_group {h : ℕ}
    (r : VariablePosition h ⊕ Fin (2 ^ h)) (t : Mode h)
    (u v : Fin 64) (x y : Fin (2 ^ h))
    (hu : host (Sum.inr r) (Sum.inl (t, u, x)) = true)
    (hv : host (Sum.inr r) (Sum.inl (t, v, y)) = true) : u = v := by
  change decide ((u.val = 0 ∧ rowRole t 0 (Sum.inr r)) ∨
    (u.val = 1 ∧ rowRole t 1 (Sum.inr r))) = true at hu
  change decide ((v.val = 0 ∧ rowRole t 0 (Sum.inr r)) ∨
    (v.val = 1 ∧ rowRole t 1 (Sum.inr r))) = true at hv
  have hu' := of_decide_eq_true hu
  have hv' := of_decide_eq_true hv
  rcases hu' with ⟨hu0, hr0⟩ | ⟨hu1, hr1⟩
  · rcases hv' with ⟨hv0, _⟩ | ⟨_, hr1⟩
    · exact Fin.ext (hu0.trans hv0.symm)
    · exact False.elim (rowRole_disjoint t (Sum.inr r) ⟨hr0, hr1⟩)
  · rcases hv' with ⟨_, hr0⟩ | ⟨hv1, _⟩
    · exact False.elim (rowRole_disjoint t (Sum.inr r) ⟨hr0, hr1⟩)
    · exact Fin.ext (hu1.trans hv1.symm)

/-- On the rows of one mode, a nonanchor column has ones in only one group. -/
theorem host_nonanchor_col_one_group {h : ℕ}
    (c : VariablePosition h ⊕ Fin (2 ^ h)) (t : Mode h)
    (u v : Fin 64) (x y : Fin (2 ^ h))
    (hu : host (Sum.inl (t, u, x)) (Sum.inr c) = true)
    (hv : host (Sum.inl (t, v, y)) (Sum.inr c) = true) : u = v := by
  change decide ((u.val = 0 ∧ colRole t 0 (Sum.inr c)) ∨
    (u.val = 1 ∧ colRole t 1 (Sum.inr c))) = true at hu
  change decide ((v.val = 0 ∧ colRole t 0 (Sum.inr c)) ∨
    (v.val = 1 ∧ colRole t 1 (Sum.inr c))) = true at hv
  have hu' := of_decide_eq_true hu
  have hv' := of_decide_eq_true hv
  rcases hu' with ⟨hu0, hc0⟩ | ⟨hu1, hc1⟩
  · rcases hv' with ⟨hv0, _⟩ | ⟨_, hc1⟩
    · exact Fin.ext (hu0.trans hv0.symm)
    · exact False.elim (colRole_disjoint t (Sum.inr c) ⟨hc0, hc1⟩)
  · rcases hv' with ⟨_, hc0⟩ | ⟨hv1, _⟩
    · exact False.elim (colRole_disjoint t (Sum.inr c) ⟨hc0, hc1⟩)
    · exact Fin.ext (hu1.trans hv1.symm)

/-- Unit-incidence premise for a selected family of columns with no repeated group. -/
theorem host_nonanchor_row_unit {h : ℕ} {J : Type uJ}
    (r : Position h) (c : J → Position h) (hcgroup : DistinctAnchorGroups c)
    (hr : positionMode r = none) (j k : J) (t : Mode h)
    (hj : positionMode (c j) = some t) (hk : positionMode (c k) = some t)
    (hbj : host r (c j) = true) (hbk : host r (c k) = true) : j = k := by
  rcases r with a | r
  · simp [positionMode] at hr
  rcases hjc : c j with ⟨tj, uj, xj⟩ | cj
  · rcases hkc : c k with ⟨tk, uk, xk⟩ | ck
    · simp only [hjc, hkc, positionMode, Option.some.injEq] at hj hk
      subst tj
      subst tk
      rw [hjc] at hbj
      rw [hkc] at hbk
      have hu := host_nonanchor_row_one_group r t uj uk xj xk hbj hbk
      apply hcgroup j k (t, uj)
      · simp [hjc, positionGroup]
      · simp [hkc, positionGroup, hu]
    · simp [hkc, positionMode] at hk
  · simp [hjc, positionMode] at hj

/-- Unit-incidence premise for a selected family of rows with no repeated group. -/
theorem host_nonanchor_col_unit {h : ℕ} {I : Type uI}
    (r : I → Position h) (c : Position h) (hrgroup : DistinctAnchorGroups r)
    (hc : positionMode c = none) (i k : I) (t : Mode h)
    (hi : positionMode (r i) = some t) (hk : positionMode (r k) = some t)
    (hbi : host (r i) c = true) (hbk : host (r k) c = true) : i = k := by
  rcases c with a | c
  · simp [positionMode] at hc
  rcases hir : r i with ⟨ti, ui, xi⟩ | ri
  · rcases hkr : r k with ⟨tk, uk, xk⟩ | rk
    · simp only [hir, hkr, positionMode, Option.some.injEq] at hi hk
      subst ti
      subst tk
      rw [hir] at hbi
      rw [hkr] at hbk
      have hu := host_nonanchor_col_one_group c t ui uk xi xk hbi hbk
      apply hrgroup i k (t, ui)
      · simp [hir, positionGroup]
      · simp [hkr, positionGroup, hu]
    · simp [hkr, positionMode] at hk
  · simp [hir, positionMode] at hi

end Problem348.AnchorRigidity


/-!
# Concrete canonical-host specialization of anchor rigidity

For `Construction.host`, a dense core forces one common anchor mode.
The twin, signature, density, and cross-mode properties follow from the
canonical entry table.
-/

namespace Problem348.HostAnchorRigidity

open Construction

/-- The mode label of an anchor, and `none` for a non-anchor. -/
def modeLabel {h : ℕ} : Position h → Option (Mode h)
  | Sum.inl (t, _, _) => some t
  | Sum.inr _ => none

/-- The actual dummy positions on either raw axis. -/
def Dummy {h : ℕ} (x : Position h) : Prop :=
  ∃ z, x = Sum.inr (Sum.inr z)

theorem exists_anchor_of_mode {h : ℕ} {x : Position h} {t : Mode h}
    (hx : modeLabel x = some t) :
    ∃ u z, x = Sum.inl (t, u, z) := by
  rcases x with ⟨t', u, z⟩ | a
  · simp only [modeLabel, Option.some.injEq] at hx
    subst t'
    exact ⟨u, z, rfl⟩
  · simp [modeLabel] at hx

theorem exists_nonanchor_of_mode_none {h : ℕ} {x : Position h}
    (hx : modeLabel x = none) :
    ∃ a, x = Sum.inr a := by
  rcases x with a | a
  · simp [modeLabel] at hx
  · exact ⟨a, rfl⟩

theorem exists_dummy_of_dummy {h : ℕ} {x : Position h} (hx : Dummy x) :
    ∃ z, x = Sum.inr (Sum.inr z) := hx

/-- Distinct selected anchor rows cannot have the same mode and group. -/
theorem selected_anchor_rows_unique {h : ℕ}
    (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    {i k : Fin 64} {t : Mode h} {u : Fin 64} {x y : Fin (2 ^ h)}
    (hi : r i = Sum.inl (t, u, x))
    (hk : r k = Sum.inl (t, u, y)) : i = k := by
  apply anchor64_rows_injective
  funext j
  rw [← hcopy i j, ← hcopy k j, hi, hk]
  exact host_anchor_row_twin t u x y (c j)

/-- Distinct selected anchor columns cannot have the same mode and group. -/
theorem selected_anchor_columns_unique {h : ℕ}
    (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    {j k : Fin 64} {t : Mode h} {v : Fin 64} {x y : Fin (2 ^ h)}
    (hj : c j = Sum.inl (t, v, x))
    (hk : c k = Sum.inl (t, v, y)) : j = k := by
  apply anchor64_columns_injective
  funext i
  change anchor64 i j = anchor64 i k
  rw [← hcopy i j, ← hcopy i k, hj, hk]
  exact host_anchor_column_twin t v x y (r i)

/-- At most one selected row can be dummy, because all dummy rows are twins. -/
theorem selected_dummy_rows_unique {h : ℕ}
    (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    {i k : Fin 64} (hi : Dummy (r i)) (hk : Dummy (r k)) : i = k := by
  obtain ⟨x, hx⟩ := exists_dummy_of_dummy hi
  obtain ⟨y, hy⟩ := exists_dummy_of_dummy hk
  apply anchor64_rows_injective
  funext j
  rw [← hcopy i j, ← hcopy k j, hx, hy]
  exact host_dummy_row_twin x y (c j)

/-- At most one selected column can be dummy. -/
theorem selected_dummy_columns_unique {h : ℕ}
    (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    {j k : Fin 64} (hj : Dummy (c j)) (hk : Dummy (c k)) : j = k := by
  obtain ⟨x, hx⟩ := exists_dummy_of_dummy hj
  obtain ⟨y, hy⟩ := exists_dummy_of_dummy hk
  apply anchor64_columns_injective
  funext i
  change anchor64 i j = anchor64 i k
  rw [← hcopy i j, ← hcopy i k, hx, hy]
  exact host_dummy_column_twin x y (r i)

/-- A one between two anchors forces their modes to coincide. -/
theorem selected_cross_mode {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (i j : Fin 64) (t u : Mode h)
    (hi : modeLabel (r i) = some t) (hj : modeLabel (c j) = some u)
    (hij : anchor64 i j = true) : t = u := by
  obtain ⟨v, x, hx⟩ := exists_anchor_of_mode hi
  obtain ⟨w, y, hy⟩ := exists_anchor_of_mode hj
  rw [← hcopy i j, hx, hy] at hij
  by_contra hne
  simp [host, hne] at hij

/-- On the selected anchors of a fixed mode a non-anchor row has at most one one. -/
theorem selected_nonanchor_row_unit {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (i : Fin 64) (hi : modeLabel (r i) = none) (j k : Fin 64) (t : Mode h)
    (hj : modeLabel (c j) = some t) (hk : modeLabel (c k) = some t)
    (hij : anchor64 i j = true) (hik : anchor64 i k = true) : j = k := by
  obtain ⟨a, hx⟩ := exists_nonanchor_of_mode_none hi
  obtain ⟨v, y, hy⟩ := exists_anchor_of_mode hj
  obtain ⟨w, z, hz⟩ := exists_anchor_of_mode hk
  rw [← hcopy i j, hx, hy] at hij
  rw [← hcopy i k, hx, hz] at hik
  have hvw : v = w := nonanchor_row_one_group_unique a t v w y z hij hik
  subst w
  exact selected_anchor_columns_unique r c hcopy hy hz

/-- On the selected anchors of a fixed mode a non-anchor column has at most one one. -/
theorem selected_nonanchor_column_unit {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (j : Fin 64) (hj : modeLabel (c j) = none) (i k : Fin 64) (t : Mode h)
    (hi : modeLabel (r i) = some t) (hk : modeLabel (r k) = some t)
    (hij : anchor64 i j = true) (hkj : anchor64 k j = true) : i = k := by
  obtain ⟨a, hx⟩ := exists_nonanchor_of_mode_none hj
  obtain ⟨u, y, hy⟩ := exists_anchor_of_mode hi
  obtain ⟨v, z, hz⟩ := exists_anchor_of_mode hk
  rw [← hcopy i j, hy, hx] at hij
  rw [← hcopy k j, hz, hx] at hkj
  have huv : u = v := nonanchor_column_one_group_unique a t u v y z hij hkj
  subst v
  exact selected_anchor_rows_unique r c hcopy hy hz

/-- Concrete host rigidity assuming a dense core, with twin, signature,
density, and cross-mode properties following from the host entries. -/
theorem mode_constant_of_dense_core {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hcore :
      AnchorRigidity.DenseAnchorCore anchor64 (modeLabel ∘ r) (modeLabel ∘ c) (Dummy ∘ c) ∨
      AnchorRigidity.DenseAnchorCore (fun j i => anchor64 i j)
        (modeLabel ∘ c) (modeLabel ∘ r) (Dummy ∘ r)) :
    ∃ t : Mode h, (∀ i, modeLabel (r i) = some t) ∧
      (∀ j, modeLabel (c j) = some t) := by
  apply AnchorRigidity.rigidity anchor64 (modeLabel ∘ r) (modeLabel ∘ c)
    (Dummy ∘ r) (Dummy ∘ c) hcore
  · intro i k hi hk
    exact selected_dummy_rows_unique r c hcopy hi hk
  · intro j k hj hk
    exact selected_dummy_columns_unique r c hcopy hj hk
  · exact selected_cross_mode r c hcopy
  · exact selected_nonanchor_row_unit r c hcopy
  · exact selected_nonanchor_column_unit r c hcopy
  · intro i
    exact (by decide : 2 ≤ 58).trans (anchor64_row_ones i)
  · intro j
    exact (by decide : 2 ≤ 48).trans (anchor64_column_ones j)

end Problem348.HostAnchorRigidity

end OAI
