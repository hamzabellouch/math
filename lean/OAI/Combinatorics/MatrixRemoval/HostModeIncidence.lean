import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.ModeIncidence

namespace OAI

/-!
The mode-incidence count bounds sparse anchor traces for the actual
finite host.
-/

universe uAlpha

namespace Problem348.Construction

private def incidenceKind (k : ℕ) : ModeIncidence.Kind :=
  if k < 2 then .vertical (decide (k = 0))
  else .horizontal (decide (k < 4)) (decide (k % 2 = 1))

/-- Decode the canonical six-mode enumeration into the incidence labels. -/
def incidenceMode {h : ℕ} (t : Mode h) : ModeIncidence.Mode :=
  (level t, incidenceKind (kind t))

/-- Boolean parity, in the convention used by ModeIncidence. -/
def nodeParity {h : ℕ} (v : VariablePosition h) : Bool :=
  decide (node v % 2 = 1)

private theorem incidenceKind_injective {a b : ℕ} (ha : a < 6) (hb : b < 6)
    (hab : incidenceKind a = incidenceKind b) : a = b := by
  interval_cases a <;> interval_cases b <;> simp_all [incidenceKind]

 theorem incidenceMode_injective (h : ℕ) :
    Function.Injective (@incidenceMode h) := by
  intro t u htu
  have hl : level t = level u := congrArg Prod.fst htu
  have hk := incidenceKind_injective (kind_lt t) (kind_lt u)
    (congrArg Prod.snd htu)
  apply Fin.ext
  dsimp [level] at hl
  dsimp [kind] at hk
  omega

 theorem rowRole_incident {h : ℕ} (t : Mode h) (j : Fin 2)
    (v : VariablePosition h) (hv : rowRole t j (.inr (.inl v))) :
    ModeIncidence.rowIncident h (depth v) (plus v) (nodeParity v)
      (incidenceMode t) := by
  have hp := level_pos t
  have hl := level_le t
  have hk := kind_lt t
  interval_cases e : kind t <;> fin_cases j <;>
    simp_all [rowRole, incidenceMode, incidenceKind, ModeIncidence.rowIncident,
      ModeIncidence.hasSign, AtLevel, nodeParity]

 theorem colRole_incident {h : ℕ} (t : Mode h) (j : Fin 2)
    (v : VariablePosition h) (hv : colRole t j (.inr (.inl v))) :
    ModeIncidence.colIncident h (depth v) (plus v) (nodeParity v)
      (incidenceMode t) := by
  have hp := level_pos t
  have hl := level_le t
  have hk := kind_lt t
  interval_cases e : kind t <;> fin_cases j <;>
    simp_all [colRole, incidenceMode, incidenceKind, ModeIncidence.colIncident,
      ModeIncidence.hasSign, AtLevel, nodeParity]

/-- The actual canonical variable row meets at most four modes. -/
theorem card_rowRole_modes_le_four {h : ℕ} (v : VariablePosition h)
    (s : Finset (Mode h))
    (hs : ∀ t ∈ s, ∃ j, rowRole t j (.inr (.inl v))) : s.card ≤ 4 := by
  rw [← Finset.card_image_of_injective s (incidenceMode_injective h)]
  apply ModeIncidence.card_row_incident_le_four (depth_le v)
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨j, hj⟩ := hs u hu
  exact rowRole_incident u j v hj

/-- The actual canonical variable column meets at most four modes. -/
theorem card_colRole_modes_le_four {h : ℕ} (v : VariablePosition h)
    (s : Finset (Mode h))
    (hs : ∀ t ∈ s, ∃ j, colRole t j (.inr (.inl v))) : s.card ≤ 4 := by
  rw [← Finset.card_image_of_injective s (incidenceMode_injective h)]
  apply ModeIncidence.card_col_incident_le_four (depth_le v)
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨j, hj⟩ := hs u hu
  exact colRole_incident u j v hj

/-- A nonanchor row has at most one one-bearing anchor group in each mode. -/
theorem row_anchor_ones_unique_group {h : ℕ}
    (x : VariablePosition h ⊕ Fin (2 ^ h))
    (a b : AnchorPosition h)
    (ha : host (.inr x) (.inl a) = true)
    (hb : host (.inr x) (.inl b) = true)
    (hm : a.1 = b.1) : a.2.1 = b.2.1 := by
  rcases a with ⟨t, u, ax⟩
  rcases b with ⟨t', v, bx⟩
  dsimp at hm ⊢
  subst t'
  simp only [host, decide_eq_true_eq] at ha hb
  rcases ha with ⟨hu, hr⟩ | ⟨hu, hr⟩ <;>
    rcases hb with ⟨hv, hs⟩ | ⟨hv, hs⟩
  · exact Fin.ext (by omega)
  · exact False.elim (rowRole_disjoint t (.inr x) ⟨hr, hs⟩)
  · exact False.elim (rowRole_disjoint t (.inr x) ⟨hs, hr⟩)
  · exact Fin.ext (by omega)

/-- The corresponding unit-signature fact for a nonanchor column. -/
theorem col_anchor_ones_unique_group {h : ℕ}
    (x : VariablePosition h ⊕ Fin (2 ^ h))
    (a b : AnchorPosition h)
    (ha : host (.inl a) (.inr x) = true)
    (hb : host (.inl b) (.inr x) = true)
    (hm : a.1 = b.1) : a.2.1 = b.2.1 := by
  rcases a with ⟨t, u, ax⟩
  rcases b with ⟨t', v, bx⟩
  dsimp at hm ⊢
  subst t'
  simp only [host, decide_eq_true_eq] at ha hb
  rcases ha with ⟨hu, hr⟩ | ⟨hu, hr⟩ <;>
    rcases hb with ⟨hv, hs⟩ | ⟨hv, hs⟩
  · exact Fin.ext (by omega)
  · exact False.elim (colRole_disjoint t (.inr x) ⟨hr, hs⟩)
  · exact False.elim (colRole_disjoint t (.inr x) ⟨hs, hr⟩)
  · exact Fin.ext (by omega)

/-- The concrete sparse-anchor-trace conclusion for arbitrary indexed anchor
representatives: no group is represented twice among the selected indices. -/
theorem card_variable_row_anchor_ones_le_four {h : ℕ} {α : Type uAlpha}
    [DecidableEq α] (v : VariablePosition h) (s : Finset α)
    (a : α → AnchorPosition h)
    (hgroups : Set.InjOn (fun x => ((a x).1, (a x).2.1)) (s : Set α)) :
    (s.filter (fun x => host (.inr (.inl v)) (.inl (a x)) = true)).card ≤ 4 := by
  classical
  apply ModeIncidence.card_row_ones_le_four
    (sign := plus v) (parity := nodeParity v) (depth_le v) s
    (fun x => incidenceMode (a x).1)
    (fun x => host (.inr (.inl v)) (.inl (a x)))
  · intro x hx hentry
    have hrole : ((a x).2.1.val = 0 ∧ rowRole (a x).1 0 (.inr (.inl v))) ∨
        ((a x).2.1.val = 1 ∧ rowRole (a x).1 1 (.inr (.inl v))) := by
      simpa only [host, decide_eq_true_eq] using hentry
    rcases hrole with ⟨_, hr⟩ | ⟨_, hr⟩
    · exact rowRole_incident (a x).1 0 v hr
    · exact rowRole_incident (a x).1 1 v hr
  · intro x hx y hy hxe hye hm
    have hm' : (a x).1 = (a y).1 := incidenceMode_injective h hm
    have hg : (a x).2.1 = (a y).2.1 :=
      row_anchor_ones_unique_group (.inl v) (a x) (a y) hxe hye hm'
    exact hgroups hx hy (Prod.ext hm' hg)

/-- The concrete sparse-anchor-trace conclusion for a variable column. -/
theorem card_variable_col_anchor_ones_le_four {h : ℕ} {α : Type uAlpha}
    [DecidableEq α] (v : VariablePosition h) (s : Finset α)
    (a : α → AnchorPosition h)
    (hgroups : Set.InjOn (fun x => ((a x).1, (a x).2.1)) (s : Set α)) :
    (s.filter (fun x => host (.inl (a x)) (.inr (.inl v)) = true)).card ≤ 4 := by
  classical
  apply ModeIncidence.card_col_ones_le_four
    (sign := plus v) (parity := nodeParity v) (depth_le v) s
    (fun x => incidenceMode (a x).1)
    (fun x => host (.inl (a x)) (.inr (.inl v)))
  · intro x hx hentry
    have hrole : ((a x).2.1.val = 0 ∧ colRole (a x).1 0 (.inr (.inl v))) ∨
        ((a x).2.1.val = 1 ∧ colRole (a x).1 1 (.inr (.inl v))) := by
      simpa only [host, decide_eq_true_eq] using hentry
    rcases hrole with ⟨_, hr⟩ | ⟨_, hr⟩
    · exact colRole_incident (a x).1 0 v hr
    · exact colRole_incident (a x).1 1 v hr
  · intro x hx y hy hxe hye hm
    have hm' : (a x).1 = (a y).1 := incidenceMode_injective h hm
    have hg : (a x).2.1 = (a y).2.1 :=
      col_anchor_ones_unique_group (.inl v) (a x) (a y) hxe hye hm'
    exact hgroups hx hy (Prod.ext hm' hg)

end Problem348.Construction

end OAI
