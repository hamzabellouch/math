import Mathlib

namespace OAI

/-!
Mode-incidence bounds. Active modes have levels 1 through h, while
variable positions have levels 0 through h. At level h the plus and minus
blocks coincide.
-/

universe uAlpha

namespace Problem348.ModeIncidence

inductive Kind where
  | vertical (sign : Bool)
  | horizontal (sign parity : Bool)
  deriving DecidableEq, Fintype

abbrev Mode := ℕ × Kind

/-- Leaf positions have both sign names; other positions have their own sign. -/
def hasSign (h depth : ℕ) (own requested : Bool) : Prop :=
  depth = h ∨ own = requested

/-- Incidence with either row role of a mode. -/
def rowIncident (h depth : ℕ) (sign parity : Bool) (t : Mode) : Prop :=
  1 ≤ t.1 ∧ t.1 ≤ h ∧
    match t.2 with
    | .vertical s => (depth = t.1 ∨ depth + 1 = t.1) ∧ hasSign h depth sign s
    | .horizontal s p => depth = t.1 ∧ hasSign h depth sign s ∧ parity = p

/-- Incidence with either column role of a mode. -/
def colIncident (h depth : ℕ) (sign parity : Bool) (t : Mode) : Prop :=
  1 ≤ t.1 ∧ t.1 ≤ h ∧
    match t.2 with
    | .vertical s => depth + 1 = t.1 ∧ hasSign h depth sign s
    | .horizontal s p => hasSign h depth sign s ∧
        (depth + 1 = t.1 ∨ (depth = t.1 ∧ parity = p))

/-- Three possible modes for an internal variable row. Boundary levels may
remove some of these modes. -/
def internalRowModes (depth : ℕ) (sign parity : Bool) : Finset Mode :=
  {(depth, .vertical sign), (depth + 1, .vertical sign),
    (depth, .horizontal sign parity)}

/-- The four possible modes for a shared leaf row. -/
def leafRowModes (h : ℕ) (parity : Bool) : Finset Mode :=
  {(h, .vertical false), (h, .vertical true),
    (h, .horizontal false parity), (h, .horizontal true parity)}

/-- Four possible modes for an internal variable column. -/
def internalColModes (depth : ℕ) (sign parity : Bool) : Finset Mode :=
  {(depth + 1, .vertical sign), (depth + 1, .horizontal sign false),
    (depth + 1, .horizontal sign true), (depth, .horizontal sign parity)}

/-- The two possible modes for a shared leaf column. -/
def leafColModes (h : ℕ) (parity : Bool) : Finset Mode :=
  {(h, .horizontal false parity), (h, .horizontal true parity)}

theorem rowIncident_internal {h depth : ℕ} {sign parity : Bool} {t : Mode}
    (hd : depth < h) (ht : rowIncident h depth sign parity t) :
    t ∈ internalRowModes depth sign parity := by
  rcases t with ⟨level, kind⟩
  rcases kind with s | ⟨s, p⟩ <;> dsimp [rowIncident] at ht
  · rcases ht with ⟨_, _, hlevel, hsign⟩
    have hs : sign = s := hsign.resolve_left (Nat.ne_of_lt hd)
    subst s
    rcases hlevel with rfl | rfl <;> simp [internalRowModes]
  · rcases ht with ⟨_, _, hlevel, hsign, hp⟩
    have hs : sign = s := hsign.resolve_left (Nat.ne_of_lt hd)
    subst s
    subst p
    subst level
    simp [internalRowModes]

theorem rowIncident_leaf {h : ℕ} {sign parity : Bool} {t : Mode}
    (ht : rowIncident h h sign parity t) : t ∈ leafRowModes h parity := by
  rcases t with ⟨level, kind⟩
  rcases kind with s | ⟨s, p⟩ <;> dsimp [rowIncident] at ht
  · rcases ht with ⟨_, hbound, hlevel, _⟩
    have heq : level = h := by omega
    subst level
    cases s <;> simp [leafRowModes]
  · rcases ht with ⟨_, _, hlevel, _, hp⟩
    subst level
    subst p
    cases s <;> simp [leafRowModes]

theorem colIncident_internal {h depth : ℕ} {sign parity : Bool} {t : Mode}
    (hd : depth < h) (ht : colIncident h depth sign parity t) :
    t ∈ internalColModes depth sign parity := by
  rcases t with ⟨level, kind⟩
  rcases kind with s | ⟨s, p⟩ <;> dsimp [colIncident] at ht
  · rcases ht with ⟨_, _, hlevel, hsign⟩
    have hs : sign = s := hsign.resolve_left (Nat.ne_of_lt hd)
    subst s
    subst level
    simp [internalColModes]
  · rcases ht with ⟨_, _, hsign, hlevel⟩
    have hs : sign = s := hsign.resolve_left (Nat.ne_of_lt hd)
    subst s
    rcases hlevel with hlevel | ⟨hlevel, hp⟩
    · subst level
      cases p <;> simp [internalColModes]
    · subst level
      subst p
      simp [internalColModes]

theorem colIncident_leaf {h : ℕ} {sign parity : Bool} {t : Mode}
    (ht : colIncident h h sign parity t) : t ∈ leafColModes h parity := by
  rcases t with ⟨level, kind⟩
  rcases kind with s | ⟨s, p⟩ <;> dsimp [colIncident] at ht
  · rcases ht with ⟨_, hbound, hlevel, _⟩
    omega
  · rcases ht with ⟨_, hbound, _, hlevel⟩
    rcases hlevel with hbad | ⟨heq, hp⟩
    · omega
    · subst level
      subst p
      cases s <;> simp [leafColModes]

/-- An internal row participates in at most three modes. -/
theorem card_internalRowModes_le (depth : ℕ) (sign parity : Bool) :
    (internalRowModes depth sign parity).card ≤ 3 := by
  simp only [internalRowModes]
  exact Finset.card_insert_le _ _ |>.trans (Nat.succ_le_succ
    (Finset.card_insert_le _ _ |>.trans (by simp)))

/-- A leaf row participates in at most four modes. -/
theorem card_leafRowModes_le (h : ℕ) (parity : Bool) :
    (leafRowModes h parity).card ≤ 4 := by
  simp [leafRowModes]

/-- A variable column below the leaf level participates in at most four modes. -/
theorem card_internalColModes_le (depth : ℕ) (sign parity : Bool) :
    (internalColModes depth sign parity).card ≤ 4 := by
  unfold internalColModes
  exact Finset.card_insert_le _ _ |>.trans (Nat.succ_le_succ
    (Finset.card_insert_le _ _ |>.trans (Nat.succ_le_succ
      (Finset.card_insert_le _ _ |>.trans (by simp)))))

/-- A leaf column participates in at most two modes. -/
theorem card_leafColModes_le (h : ℕ) (parity : Bool) :
    (leafColModes h parity).card ≤ 2 := by
  simp [leafColModes]

/-- Formulation independent of the particular finite enumeration of valid modes. -/
theorem card_row_incident_le_four {h depth : ℕ} {sign parity : Bool}
    (hd : depth ≤ h) (modes : Finset Mode)
    (hmodes : ∀ t ∈ modes, rowIncident h depth sign parity t) :
    modes.card ≤ 4 := by
  rcases lt_or_eq_of_le hd with hd | rfl
  · have hsub : modes ⊆ internalRowModes depth sign parity := by
      intro t ht
      exact rowIncident_internal hd (hmodes t ht)
    exact (Finset.card_le_card hsub).trans
      ((card_internalRowModes_le depth sign parity).trans (by decide))
  · have hsub : modes ⊆ leafRowModes depth parity := by
      intro t ht
      exact rowIncident_leaf (hmodes t ht)
    exact (Finset.card_le_card hsub).trans (card_leafRowModes_le depth parity)

/-- Formulation independent of the particular finite enumeration of valid modes. -/
theorem card_col_incident_le_four {h depth : ℕ} {sign parity : Bool}
    (hd : depth ≤ h) (modes : Finset Mode)
    (hmodes : ∀ t ∈ modes, colIncident h depth sign parity t) :
    modes.card ≤ 4 := by
  rcases lt_or_eq_of_le hd with hd | rfl
  · have hsub : modes ⊆ internalColModes depth sign parity := by
      intro t ht
      exact colIncident_internal hd (hmodes t ht)
    exact (Finset.card_le_card hsub).trans (card_internalColModes_le depth sign parity)
  · have hsub : modes ⊆ leafColModes depth parity := by
      intro t ht
      exact colIncident_leaf (hmodes t ht)
    exact (Finset.card_le_card hsub).trans
      ((card_leafColModes_le depth parity).trans (by decide))

/-- A generic sparse-trace transfer: at most one chosen one-entry per mode. -/
theorem card_ones_le_of_mode_bound {α : Type uAlpha} [DecidableEq α]
    (positions : Finset α) (mode : α → Mode) (entry : α → Bool)
    (incident : Mode → Prop) (bound : ℕ)
    (hbound : ∀ modes : Finset Mode,
      (∀ t ∈ modes, incident t) → modes.card ≤ bound)
    (hincident : ∀ x ∈ positions, entry x = true → incident (mode x))
    (hunique : ∀ x ∈ positions, ∀ y ∈ positions,
      entry x = true → entry y = true → mode x = mode y → x = y) :
    (positions.filter (fun x => entry x = true)).card ≤ bound := by
  have hinjective : Set.InjOn mode
      (↑(positions.filter (fun x => entry x = true)) : Set α) := by
    intro x hx y hy heq
    obtain ⟨hx, hxe⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hye⟩ := Finset.mem_filter.mp hy
    exact hunique x hx y hy hxe hye heq
  rw [← Finset.card_image_of_injOn hinjective]
  apply hbound
  intro t ht
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hx, hxe⟩ := Finset.mem_filter.mp hx
  exact hincident x hx hxe

/-- Against anchor representatives, a variable row has at most four ones,
provided one-entries in the same mode use the same representative. -/
theorem card_row_ones_le_four {α : Type uAlpha} [DecidableEq α]
    {h depth : ℕ} {sign parity : Bool} (hd : depth ≤ h)
    (positions : Finset α) (mode : α → Mode) (entry : α → Bool)
    (hincident : ∀ x ∈ positions, entry x = true →
      rowIncident h depth sign parity (mode x))
    (hunique : ∀ x ∈ positions, ∀ y ∈ positions,
      entry x = true → entry y = true → mode x = mode y → x = y) :
    (positions.filter (fun x => entry x = true)).card ≤ 4 :=
  card_ones_le_of_mode_bound positions mode entry
    (rowIncident h depth sign parity) 4
    (card_row_incident_le_four hd) hincident hunique

/-- The symmetric sparse-trace statement for variable columns. -/
theorem card_col_ones_le_four {α : Type uAlpha} [DecidableEq α]
    {h depth : ℕ} {sign parity : Bool} (hd : depth ≤ h)
    (positions : Finset α) (mode : α → Mode) (entry : α → Bool)
    (hincident : ∀ x ∈ positions, entry x = true →
      colIncident h depth sign parity (mode x))
    (hunique : ∀ x ∈ positions, ∀ y ∈ positions,
      entry x = true → entry y = true → mode x = mode y → x = y) :
    (positions.filter (fun x => entry x = true)).card ≤ 4 :=
  card_ones_le_of_mode_bound positions mode entry
    (colIncident h depth sign parity) 4
    (card_col_incident_le_four hd) hincident hunique

end Problem348.ModeIncidence

end OAI
