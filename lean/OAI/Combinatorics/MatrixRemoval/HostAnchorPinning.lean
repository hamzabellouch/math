import OAI.Combinatorics.MatrixRemoval.HostAnchorRigidity
import OAI.Combinatorics.MatrixRemoval.AnchorRigidityFixed
import OAI.Combinatorics.MatrixRemoval.AnchorPatternFixed
import OAI.Combinatorics.MatrixRemoval.HostNonshattering

namespace OAI

/-! Assembly of the exact anchor-majority and concrete-host rigidity steps. -/
namespace Problem348.HostAnchorRigidity

open Construction AnchorRigidity

/-- An exact anchor copy is automatically injective on the column axis. -/
theorem selected_columns_injective {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) : Function.Injective c := by
  intro j k hjk
  apply anchor64_columns_injective
  funext i
  change anchor64 i j = anchor64 i k
  rw [← hcopy i j, ← hcopy i k, hjk]

/-- An exact anchor copy is automatically injective on the row axis. -/
theorem selected_rows_injective {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) : Function.Injective r := by
  intro i k hik
  apply anchor64_rows_injective
  funext j
  rw [← hcopy i j, ← hcopy k j, hik]

/-- Variable-column sparseness on a selected prefix. -/
def ColumnSparse {h : ℕ} (r c : Fin 64 → Position h) : Prop :=
  ∀ j, modeLabel (c j) = none → ¬ Dummy (c j) →
    (∀ i ∈ firstCore, ∃ t, modeLabel (r i) = some t) →
    (firstCore.filter fun i => anchor64 i j = true).card ≤ 4

/-- Variable-row sparseness on a selected prefix. -/
def RowSparse {h : ℕ} (r c : Fin 64 → Position h) : Prop :=
  ∀ i, modeLabel (r i) = none → ¬ Dummy (r i) →
    (∀ j ∈ firstCore, ∃ t, modeLabel (c j) = some t) →
    (firstCore.filter fun j => anchor64 i j = true).card ≤ 4

/-- Prefix anchoring plus actual variable sparseness pins all positions to one mode. -/
theorem mode_constant_of_prefix {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hprefix : (∀ i : Fin 64, i.val < 32 → ∃ t, modeLabel (r i) = some t) ∨
      (∀ j : Fin 64, j.val < 32 → ∃ t, modeLabel (c j) = some t))
    (hcs : ColumnSparse r c) (hrs : RowSparse r c) :
    ∃ t : Mode h, (∀ i, modeLabel (r i) = some t) ∧
      (∀ j, modeLabel (c j) = some t) := by
  apply anchor64_rigidity_of_prefix (modeLabel ∘ r) (modeLabel ∘ c)
    (Dummy ∘ r) (Dummy ∘ c) hprefix hcs hrs
  · intro i k hi hk
    exact selected_dummy_rows_unique r c hcopy hi hk
  · intro j k hj hk
    exact selected_dummy_columns_unique r c hcopy hj hk
  · exact selected_cross_mode r c hcopy
  · exact selected_nonanchor_row_unit r c hcopy
  · exact selected_nonanchor_column_unit r c hcopy

/-- No five-column shattering and the anchor-before-nonanchor order give a
majority; prefix rigidity then yields one common mode. -/
theorem mode_constant_of_no_shattering {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (row_initial : ∀ i j, i ≤ j → modeLabel (r j) ≠ none → modeLabel (r i) ≠ none)
    (col_initial : ∀ i j, i ≤ j → modeLabel (c j) ≠ none → modeLabel (c i) ≠ none)
    (hnoshatter : ∀ cs : Fin 5 → Position h, Function.Injective cs →
      (∀ b, modeLabel (cs b) = none) → ∃ w : Fin 5 → Bool,
        ∀ x, modeLabel x = none → ∃ b, host x (cs b) ≠ w b)
    (hcs : ColumnSparse r c) (hrs : RowSparse r c) :
    ∃ t : Mode h, (∀ i, modeLabel (r i) = some t) ∧
      (∀ j, modeLabel (c j) = some t) := by
  classical
  have hm := AnchorBridge.anchor64_anchor_majority host r c
    (fun x => modeLabel x ≠ none) (fun x => modeLabel x ≠ none)
    hcopy (selected_columns_injective r c hcopy) row_initial col_initial
    (by
      intro cs hcs hnone
      obtain ⟨w, hw⟩ := hnoshatter cs hcs (fun b => not_not.mp (hnone b))
      exact ⟨w, fun x hx => hw x (not_not.mp hx)⟩)
  have hm' :
      32 < (Finset.univ.filter fun i => (modeLabel (r i)).isSome).card ∨
      32 < (Finset.univ.filter fun j => (modeLabel (c j)).isSome).card := by
    simpa only [Option.isSome_iff_ne_none, Nat.lt_iff_add_one_le] using hm
  have hp := prefix_alternative_of_majority (modeLabel ∘ r) (modeLabel ∘ c)
    row_initial col_initial hm'
  exact mode_constant_of_prefix r c hcopy hp hcs hrs

/-- The within-mode group order enjoyed by an increasingly selected axis. -/
def GroupsMonotone {h : ℕ} (r : Fin 64 → Position h) : Prop :=
  ∀ (i j : Fin 64), i ≤ j → ∀ (t : Mode h) (u v : Fin 64)
    (x y : Fin (2 ^ h)), r i = Sum.inl (t, u, x) →
      r j = Sum.inl (t, v, y) → u ≤ v

/-- Once one common mode is known, group uniqueness and the actual group
order identify its representatives in the exact pattern order. -/
theorem representatives_of_mode_constant {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hrow : GroupsMonotone r) (hcol : GroupsMonotone c)
    {t : Mode h} (hmr : ∀ i, modeLabel (r i) = some t)
    (hmc : ∀ j, modeLabel (c j) = some t) :
    ∃ a b : Fin 64 → Fin (2 ^ h),
      (∀ i, r i = Sum.inl (t, i, a i)) ∧
      (∀ j, c j = Sum.inl (t, j, b j)) := by
  classical
  choose u a ha using fun i => exists_anchor_of_mode (hmr i)
  choose v b hb using fun j => exists_anchor_of_mode (hmc j)
  have hu : Monotone u := by
    intro i j hij
    exact hrow i j hij t (u i) (u j) (a i) (a j) (ha i) (ha j)
  have hv : Monotone v := by
    intro i j hij
    exact hcol i j hij t (v i) (v j) (b i) (b j) (hb i) (hb j)
  have hui : Function.Injective u := by
    intro i j hij
    apply selected_anchor_rows_unique r c hcopy (ha i)
    simpa only [hij] using ha j
  have hvi : Function.Injective v := by
    intro i j hij
    apply selected_anchor_columns_unique r c hcopy (hb i)
    simpa only [hij] using hb j
  have hu_id : ∀ i, u i = i := by
    intro i
    have hs := hu.strictMono_of_injective hui
    exact le_antisymm (hs.le_id i) (hs.id_le i)
  have hv_id : ∀ i, v i = i := by
    intro i
    have hs := hv.strictMono_of_injective hvi
    exact le_antisymm (hs.le_id i) (hs.id_le i)
  refine ⟨a, b, ?_, ?_⟩
  · intro i
    simpa only [hu_id i] using ha i
  · intro j
    simpa only [hv_id j] using hb j

/-- Full anchor representative conclusion assuming initial anchor segments,
nonshattering, variable sparseness, and within-mode group order. -/
theorem representatives_of_no_shattering {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (row_initial : ∀ i j, i ≤ j → modeLabel (r j) ≠ none → modeLabel (r i) ≠ none)
    (col_initial : ∀ i j, i ≤ j → modeLabel (c j) ≠ none → modeLabel (c i) ≠ none)
    (hnoshatter : ∀ cs : Fin 5 → Position h, Function.Injective cs →
      (∀ b, modeLabel (cs b) = none) → ∃ w : Fin 5 → Bool,
        ∀ x, modeLabel x = none → ∃ b, host x (cs b) ≠ w b)
    (hcs : ColumnSparse r c) (hrs : RowSparse r c)
    (hrow : GroupsMonotone r) (hcol : GroupsMonotone c) :
    ∃ (t : Mode h) (a b : Fin 64 → Fin (2 ^ h)),
      (∀ i, r i = Sum.inl (t, i, a i)) ∧
      (∀ j, c j = Sum.inl (t, j, b j)) := by
  obtain ⟨t, hmr, hmc⟩ := mode_constant_of_no_shattering r c hcopy
    row_initial col_initial hnoshatter hcs hrs
  obtain ⟨a, b, ha, hb⟩ := representatives_of_mode_constant r c hcopy hrow hcol hmr hmc
  exact ⟨t, a, b, ha, hb⟩

/-- The concrete canonical host supplies the missing-word hypothesis,
without any ordering or injectivity condition on the five columns. -/
theorem actual_nonshattering {h : ℕ} (cs : Fin 5 → Position h)
    (hcs : ∀ b, modeLabel (cs b) = none) :
    ∃ w : Fin 5 → Bool, ∀ x, modeLabel x = none →
      ∃ b, host x (cs b) ≠ w b := by
  classical
  obtain ⟨w, hw⟩ := host_nonanchor_missing_word cs
    (fun b => exists_nonanchor_of_mode_none (hcs b))
  refine ⟨w, ?_⟩
  intro x hx
  have hne := hw x (exists_nonanchor_of_mode_none hx)
  by_contra heq
  push Not at heq
  exact hne (funext heq)

/-- Concrete-host anchor pinning assuming axis-order and sparse-core
conditions; nonshattering follows from the host entries. -/
theorem representatives_of_sparse {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (row_initial : ∀ i j, i ≤ j → modeLabel (r j) ≠ none → modeLabel (r i) ≠ none)
    (col_initial : ∀ i j, i ≤ j → modeLabel (c j) ≠ none → modeLabel (c i) ≠ none)
    (hcs : ColumnSparse r c) (hrs : RowSparse r c)
    (hrow : GroupsMonotone r) (hcol : GroupsMonotone c) :
    ∃ (t : Mode h) (a b : Fin 64 → Fin (2 ^ h)),
      (∀ i, r i = Sum.inl (t, i, a i)) ∧
      (∀ j, c j = Sum.inl (t, j, b j)) := by
  exact representatives_of_no_shattering r c hcopy row_initial col_initial
    (fun cs _ hin => actual_nonshattering cs hin) hcs hrs hrow hcol

end Problem348.HostAnchorRigidity

end OAI
