import Mathlib

namespace OAI

/-!
# Structural bridges for anchor pinning

Group uniqueness and no-shattering give pinning criteria independent of
the host construction.
-/

universe uI uJ uR uC uG

namespace Problem348.AnchorBridge

/-- Distinct pattern rows prevent a copy from repeating any host row class
whose members have identical entries. -/
theorem row_labels_injective {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} {G : Type uG}
    (H : I → J → Bool) (A : R → C → Bool)
    (row : I → R) (col : J → C) (label : R → G)
    (hcopy : ∀ i j, A (row i) (col j) = H i j)
    (hrows : Function.Injective H)
    (hlabel : ∀ r s, label r = label s → A r = A s) :
    Function.Injective (fun i => label (row i)) := by
  intro i j hij
  apply hrows
  funext c
  rw [← hcopy, ← hcopy]
  exact congrFun (hlabel (row i) (row j) hij) (col c)

/-- The column version of `row_labels_injective`. -/
theorem col_labels_injective {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} {G : Type uG}
    (H : I → J → Bool) (A : R → C → Bool)
    (row : I → R) (col : J → C) (label : C → G)
    (hcopy : ∀ i j, A (row i) (col j) = H i j)
    (hcols : Function.Injective (fun j => fun i => H i j))
    (hlabel : ∀ c d, label c = label d → ∀ r, A r c = A r d) :
    Function.Injective (fun j => label (col j)) := by
  intro i j hij
  apply hcols
  funext r
  change H r i = H r j
  rw [← hcopy, ← hcopy]
  exact hlabel (col i) (col j) hij (row r)

/-- The 32 rows carrying all binary words in the fixed anchor. -/
def wordRow (a : Fin 32) : Fin 64 := ⟨32 + a.val, by omega⟩

/-- The five columns carrying the word coordinates in the fixed anchor. -/
def wordCol (b : Fin 5) : Fin 64 := ⟨59 + b.val, by omega⟩

@[simp] theorem wordCol_injective : Function.Injective wordCol := by
  intro a b hab
  apply Fin.ext
  have := congrArg Fin.val hab
  simp only [wordCol] at this
  omega

/-- If both axes had at most 32 initial anchor positions, the complete-word
submatrix would shatter five non-anchor columns.  Thus the position at index
32 is an anchor on at least one axis. -/
theorem anchor_at_32_or_anchor_at_32 {R : Type uR} {C : Type uC}
    (H : Fin 64 → Fin 64 → Bool) (A : R → C → Bool)
    (row : Fin 64 → R) (col : Fin 64 → C)
    (anchorR : R → Prop) (anchorC : C → Prop)
    (hcopy : ∀ i j, A (row i) (col j) = H i j)
    (hcol : Function.Injective col)
    (hprefixR : ∀ i j, i ≤ j → anchorR (row j) → anchorR (row i))
    (hprefixC : ∀ i j, i ≤ j → anchorC (col j) → anchorC (col i))
    (hwords : ∀ w : Fin 5 → Bool, ∃ a : Fin 32,
      ∀ b : Fin 5, H (wordRow a) (wordCol b) = w b)
    (hnoshatter : ∀ cs : Fin 5 → C, Function.Injective cs →
      (∀ b, ¬ anchorC (cs b)) → ∃ w : Fin 5 → Bool,
        ∀ r, ¬ anchorR r → ∃ b, A r (cs b) ≠ w b) :
    anchorR (row ⟨32, by decide⟩) ∨ anchorC (col ⟨32, by decide⟩) := by
  classical
  by_contra h
  push Not at h
  have hr : ∀ a : Fin 32, ¬ anchorR (row (wordRow a)) := by
    intro a ha
    apply h.1
    exact hprefixR _ _ (by simp only [wordRow, Fin.le_iff_val_le_val]; omega) ha
  have hc : ∀ b : Fin 5, ¬ anchorC (col (wordCol b)) := by
    intro b hb
    apply h.2
    exact hprefixC _ _ (by simp only [wordCol, Fin.le_iff_val_le_val]; omega) hb
  obtain ⟨w, hw⟩ := hnoshatter (fun b => col (wordCol b))
    (hcol.comp wordCol_injective) hc
  obtain ⟨a, ha⟩ := hwords w
  obtain ⟨b, hb⟩ := hw (row (wordRow a)) (hr a)
  exact hb ((hcopy _ _).trans (ha b))

/-- A downward-closed predicate holding at index `m` holds at at least
`m+1` indices. -/
theorem prefix_card_lower_bound {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (m : Fin n) (hprefix : ∀ i j, i ≤ j → P j → P i) (hm : P m) :
    m.val + 1 ≤ (Finset.univ.filter P).card := by
  classical
  calc
    m.val + 1 = (Finset.Iic m).card := by simp
    _ ≤ (Finset.univ.filter P).card := by
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        hprefix i m (Finset.mem_Iic.mp hi) hm⟩

/-- An increasing self-map of a finite ordered interval uses every label
in the prescribed order. -/
theorem increasing_labels_eq_id {n : ℕ} (f : Fin n → Fin n)
    (hf : StrictMono f) : f = id := by
  funext i
  exact le_antisymm (hf.le_id i) (hf.id_le i)

/-- Any class of host rows with identical entries is used at most once
in a copy with distinct pattern rows. In particular this applies to the
dummy row class. -/
theorem card_selected_row_class_le_one {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC}
    [Fintype I] (H : I → J → Bool) (A : R → C → Bool)
    (row : I → R) (col : J → C) (P : R → Prop) [DecidablePred P]
    (hcopy : ∀ i j, A (row i) (col j) = H i j)
    (hrows : Function.Injective H)
    (hclass : ∀ r s, P r → P s → A r = A s) :
    (Finset.univ.filter (fun i => P (row i))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply hrows
  funext c
  rw [← hcopy, ← hcopy]
  exact congrFun (hclass (row i) (row j)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2) (col c)

/-- Column version of the single-use class bound. -/
theorem card_selected_col_class_le_one {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC}
    [Fintype J] (H : I → J → Bool) (A : R → C → Bool)
    (row : I → R) (col : J → C) (P : C → Prop) [DecidablePred P]
    (hcopy : ∀ i j, A (row i) (col j) = H i j)
    (hcols : Function.Injective (fun j => fun i => H i j))
    (hclass : ∀ c d, P c → P d → ∀ r, A r c = A r d) :
    (Finset.univ.filter (fun j => P (col j))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply hcols
  funext r
  change H r i = H r j
  rw [← hcopy, ← hcopy]
  exact hclass (col i) (col j)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 (row r)

end Problem348.AnchorBridge

end OAI
