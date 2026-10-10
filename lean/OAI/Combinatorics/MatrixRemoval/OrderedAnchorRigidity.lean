import OAI.Combinatorics.MatrixRemoval.HostAnchorPinning
import OAI.Combinatorics.MatrixRemoval.SelectedAnchorSparsity
import OAI.Combinatorics.MatrixRemoval.OrderedAnchorGroups

namespace OAI

/-!
# Anchor rigidity for the ordered canonical host

No-shattering, sparse anchor traces, twin classes, and the two independent
axis orders determine all anchor representatives.
-/
namespace Problem348.HostAnchorRigidity
open Construction AnchorRigidity

theorem modeLabel_eq_selectedMode {h : ℕ} (x : Position h) :
    modeLabel x = SelectedAnchors.mode x := by
  rcases x with ⟨t,u,z⟩ | a <;> rfl

theorem selected_rows_groupInjective {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) :
    SelectedAnchors.GroupInjective r := by
  intro i j a b hi hj hm hg
  rcases a with ⟨t,u,x⟩
  rcases b with ⟨s,v,y⟩
  dsimp at hm hg
  subst s
  subst v
  exact selected_anchor_rows_unique r c hcopy hi hj

theorem selected_columns_groupInjective {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) :
    SelectedAnchors.GroupInjective c := by
  intro i j a b hi hj hm hg
  rcases a with ⟨t,u,x⟩
  rcases b with ⟨s,v,y⟩
  dsimp at hm hg
  subst s
  subst v
  exact selected_anchor_columns_unique r c hcopy hi hj

/-- The sparse-column requirement follows from the actual host incidence bound. -/
theorem actual_columnSparse {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) : ColumnSparse r c := by
  intro j hm hd ha
  have hb := SelectedAnchors.sparse_column_of_mode_none r firstCore (c j)
    (by
      intro i hi
      obtain ⟨t, ht⟩ := ha i hi
      obtain ⟨u,x,hx⟩ := exists_anchor_of_mode ht
      exact ⟨(t,u,x),hx⟩)
    (selected_rows_groupInjective r c hcopy)
    (by simpa only [modeLabel_eq_selectedMode] using hm) hd
  simpa only [hcopy] using hb

/-- The transpose sparse-row requirement, with no assumptions left over. -/
theorem actual_rowSparse {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) : RowSparse r c := by
  intro i hm hd ha
  have hb := SelectedAnchors.sparse_row_of_mode_none c firstCore (r i)
    (by
      intro j hj
      obtain ⟨t, ht⟩ := ha j hj
      obtain ⟨u,x,hx⟩ := exists_anchor_of_mode ht
      exact ⟨(t,u,x),hx⟩)
    (selected_columns_groupInjective r c hcopy)
    (by simpa only [modeLabel_eq_selectedMode] using hm) hd
  simpa only [hcopy] using hb

private theorem mode_nonempty_iff_anchor {h : ℕ} (x : Position h) :
    modeLabel x ≠ none ↔ ∃ a, x = Sum.inl a := by
  rcases x with ⟨t,u,z⟩ | a <;> simp [modeLabel]

theorem row_initial_of_indices {h : ℕ} (r : Fin 64 → Position h)
    (hr : StrictMono (fun i => OrderedHost.rowIndex h (r i))) :
    ∀ i j, i ≤ j → modeLabel (r j) ≠ none → modeLabel (r i) ≠ none := by
  intro i j hij hj
  rcases eq_or_lt_of_le hij with he | hlt
  · simpa only [he] using hj
  · apply (mode_nonempty_iff_anchor (r i)).mpr
    exact OrderedHost.row_anchor_initial (hr hlt)
      ((mode_nonempty_iff_anchor (r j)).mp hj)

theorem col_initial_of_indices {h : ℕ} (c : Fin 64 → Position h)
    (hc : StrictMono (fun i => OrderedHost.columnIndex h (c i))) :
    ∀ i j, i ≤ j → modeLabel (c j) ≠ none → modeLabel (c i) ≠ none := by
  intro i j hij hj
  rcases eq_or_lt_of_le hij with he | hlt
  · simpa only [he] using hj
  · apply (mode_nonempty_iff_anchor (c i)).mpr
    exact OrderedHost.column_anchor_initial (hc hlt)
      ((mode_nonempty_iff_anchor (c j)).mp hj)

/-- Every ordered copy of the fixed 64-by-64 anchor in the canonical host
uses precisely one mode, with its groups in the prescribed order. There are
no sparsity, majority, nonshattering, twin, or abstract-order premises. -/
theorem representatives_of_indices {h : ℕ} (r c : Fin 64 → Position h)
    (hr : StrictMono (fun i => OrderedHost.rowIndex h (r i)))
    (hc : StrictMono (fun j => OrderedHost.columnIndex h (c j)))
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) :
    ∃ (t : Mode h) (a b : Fin 64 → Fin (2 ^ h)),
      (∀ i, r i = Sum.inl (t,i,a i)) ∧
      (∀ j, c j = Sum.inl (t,j,b j)) := by
  obtain ⟨t, hmr, hmc⟩ := mode_constant_of_no_shattering r c hcopy
    (row_initial_of_indices r hr) (col_initial_of_indices c hc)
    (fun cs _ hnone => actual_nonshattering cs hnone)
    (actual_columnSparse r c hcopy) (actual_rowSparse r c hcopy)
  obtain ⟨a,b,ha,hb⟩ := OrderedHost.anchor_representatives_of_one_mode
    r c t hr hc hcopy (fun i => exists_anchor_of_mode (hmr i))
    (fun j => exists_anchor_of_mode (hmc j))
  exact ⟨t,a,b,ha,hb⟩

end Problem348.HostAnchorRigidity

end OAI
