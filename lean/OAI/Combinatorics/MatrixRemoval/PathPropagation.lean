import Mathlib

namespace OAI

/-!
Boolean propagation independent of the host construction.
No entry between variable positions is assumed to remain unchanged. Only
the dummy incidences, root bits, and identification of the two leaves
are hypotheses.
-/

universe uR uC

namespace Problem348.PathPropagation

variable {R : Type uR} {C : Type uC}

/-- The lower-right two-by-two pattern of the fixed matrix `fixedH`. -/
def Body (B : R → C → Bool) (r₁ r₂ : R) (c₁ c₂ : C) : Prop :=
  B r₁ c₁ = true ∧ B r₁ c₂ = false ∧
    B r₂ c₁ = true ∧ B r₂ c₂ = true

/-- Avoiding the body propagates a one upwards across a column of dummy ones. -/
theorem vertical_plus {B : R → C → Bool} {r₁ r₂ : R} {c₁ c₂ : C}
    (havoid : ¬ Body B r₁ r₂ c₁ c₂)
    (h₁ : B r₁ c₁ = true) (h₂ : B r₂ c₁ = true)
    (h₃ : B r₂ c₂ = true) : B r₁ c₂ = true := by
  apply Bool.eq_true_of_not_eq_false
  intro h
  exact havoid ⟨h₁, h, h₂, h₃⟩

/-- Avoiding the body propagates a zero downwards across dummy ones. -/
theorem vertical_minus {B : R → C → Bool} {r₁ r₂ : R} {c₁ c₂ : C}
    (havoid : ¬ Body B r₁ r₂ c₁ c₂)
    (h₁ : B r₁ c₁ = true) (h₂ : B r₂ c₁ = true)
    (h₃ : B r₁ c₂ = false) : B r₂ c₂ = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  exact havoid ⟨h₁, h₃, h₂, h⟩

/-- Avoiding the body propagates a one rightwards above a dummy row. -/
theorem horizontal_plus {B : R → C → Bool} {r₁ r₂ : R} {c₁ c₂ : C}
    (havoid : ¬ Body B r₁ r₂ c₁ c₂)
    (h₁ : B r₁ c₁ = true) (h₂ : B r₂ c₁ = true)
    (h₃ : B r₂ c₂ = true) : B r₁ c₂ = true :=
  vertical_plus havoid h₁ h₂ h₃

/-- Avoiding the body propagates a zero leftwards above a dummy row. -/
theorem horizontal_minus {B : R → C → Bool} {r₁ r₂ : R} {c₁ c₂ : C}
    (havoid : ¬ Body B r₁ r₂ c₁ c₂)
    (h₁ : B r₁ c₂ = false) (h₂ : B r₂ c₁ = true)
    (h₃ : B r₂ c₂ = true) : B r₁ c₁ = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  exact havoid ⟨h, h₁, h₂, h₃⟩

/-- One of the four mode bodies encountered at the edge from level `i`
to level `i + 1` of the selected path. -/
def ModeBody (B : R → C → Bool)
    (xp xm : ℕ → R) (yp ym : ℕ → C) (xd : R) (yd : C) (i : ℕ) : Prop :=
  Body B (xp (i + 1)) (xp i) yd (yp i) ∨
  Body B (xm i) (xm (i + 1)) yd (ym i) ∨
  Body B (xp (i + 1)) xd (yp i) (yp (i + 1)) ∨
  Body B (xm (i + 1)) xd (ym (i + 1)) (ym i)

/-- The induction invariant: absence of all four mode bodies preserves the
opposite plus and minus bits at every level of the selected path. -/
theorem propagate {B : R → C → Bool}
    {xp xm : ℕ → R} {yp ym : ℕ → C} {xd : R} {yd : C} {h : ℕ}
    (hrootp : B (xp 0) (yp 0) = true)
    (hrootm : B (xm 0) (ym 0) = false)
    (hdcol : ∀ i, i ≤ h → B (xp i) yd = true ∧ B (xm i) yd = true)
    (hdrow : ∀ i, i ≤ h → B xd (yp i) = true ∧ B xd (ym i) = true)
    (havoid : ∀ i, i < h → ¬ ModeBody B xp xm yp ym xd yd i) :
    ∀ i, i ≤ h → B (xp i) (yp i) = true ∧ B (xm i) (ym i) = false := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨hrootp, hrootm⟩
  | succ i ih =>
      intro hi
      have hil : i ≤ h := by omega
      have hit : i < h := by omega
      obtain ⟨hp, hm⟩ := ih hil
      have hvp : ¬ Body B (xp (i + 1)) (xp i) yd (yp i) :=
        fun hb => havoid i hit (Or.inl hb)
      have hvm : ¬ Body B (xm i) (xm (i + 1)) yd (ym i) :=
        fun hb => havoid i hit (Or.inr (Or.inl hb))
      have hwp : ¬ Body B (xp (i + 1)) xd (yp i) (yp (i + 1)) :=
        fun hb => havoid i hit (Or.inr (Or.inr (Or.inl hb)))
      have hwm : ¬ Body B (xm (i + 1)) xd (ym (i + 1)) (ym i) :=
        fun hb => havoid i hit (Or.inr (Or.inr (Or.inr hb)))
      have hcrossp : B (xp (i + 1)) (yp i) = true :=
        vertical_plus hvp (hdcol (i + 1) hi).1 (hdcol i hil).1 hp
      have hcrossm : B (xm (i + 1)) (ym i) = false :=
        vertical_minus hvm (hdcol i hil).2 (hdcol (i + 1) hi).2 hm
      exact ⟨horizontal_plus hwp hcrossp (hdrow i hil).1 (hdrow (i + 1) hi).1,
        horizontal_minus hwm hcrossm (hdrow (i + 1) hi).2 (hdrow i hil).2⟩

/-- Opposite root entries and shared leaves force some mode body. Arbitrary
changes to every other variable-variable entry are explicitly allowed. -/
theorem exists_modeBody {B : R → C → Bool}
    {xp xm : ℕ → R} {yp ym : ℕ → C} {xd : R} {yd : C} {h : ℕ}
    (hrootp : B (xp 0) (yp 0) = true)
    (hrootm : B (xm 0) (ym 0) = false)
    (hdcol : ∀ i, i ≤ h → B (xp i) yd = true ∧ B (xm i) yd = true)
    (hdrow : ∀ i, i ≤ h → B xd (yp i) = true ∧ B xd (ym i) = true)
    (hleafr : xp h = xm h) (hleafc : yp h = ym h) :
    ∃ i, i < h ∧ ModeBody B xp xm yp ym xd yd i := by
  by_contra hnone
  have havoid : ∀ i, i < h → ¬ ModeBody B xp xm yp ym xd yd i := by
    intro i hi hb
    exact hnone ⟨i, hi, hb⟩
  obtain ⟨hp, hm⟩ := propagate hrootp hrootm hdcol hdrow havoid h le_rfl
  rw [hleafr, hleafc, hm] at hp
  cases hp

end Problem348.PathPropagation

end OAI
