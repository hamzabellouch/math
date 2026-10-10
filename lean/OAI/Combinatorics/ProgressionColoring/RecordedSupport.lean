import Mathlib.Data.Fintype.Card

namespace OAI

/-!
# Literal support of recorded patterns

A pattern records either a label or `none` at each position. Its support is
exactly the set of recorded labels. If no recorded label occurs twice, counting
labels is equivalent to counting regular positions, also after restricting to
one color. Thus quarter-balancing the support balances the actual positions.
-/

universe uLabel

namespace QuantitativeVanDerWaerden.RecordedSupport

variable {Label : Type uLabel} [Fintype Label] [DecidableEq Label] {h : ℕ}

/-- The labels literally recorded by the pattern. -/
noncomputable def support (p : Fin h → Option Label) : Finset Label := by
  classical
  exact Finset.univ.filter fun β => ∃ j, p j = some β

/-- A position is regular exactly when the pattern records a label there. -/
noncomputable def regularPositions (p : Fin h → Option Label) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter fun j => p j ≠ none

/-- Positions at which the recorded label satisfies a specified predicate. -/
noncomputable def positionsWhere (p : Fin h → Option Label) (q : Label → Prop) :
    Finset (Fin h) := by
  classical
  exact Finset.univ.filter fun j => ∃ β, p j = some β ∧ q β

/-- Actual positions carrying a label of the specified color. -/
noncomputable def coloredPositions (p : Fin h → Option Label)
    (color : Label → Bool) (b : Bool) : Finset (Fin h) :=
  positionsWhere p fun β => color β = b

/-- No literal label is recorded at two different positions. -/
def LabelsInjective (p : Fin h → Option Label) : Prop :=
  ∀ a b β, p a = some β → p b = some β → a = b

@[simp] theorem mem_support (p : Fin h → Option Label) (β : Label) :
    β ∈ support p ↔ ∃ j, p j = some β := by
  classical
  simp [support]

@[simp] theorem mem_regularPositions {Label : Type uLabel} [Fintype Label] [DecidableEq Label] {h : ℕ}
    (p : Fin h → Option Label) (j : Fin h) :
    j ∈ regularPositions p ↔ p j ≠ none := by
  classical
  simp [regularPositions]

@[simp] theorem mem_positionsWhere {Label : Type uLabel} [Fintype Label] [DecidableEq Label] {h : ℕ}
    (p : Fin h → Option Label)
    (q : Label → Prop) (j : Fin h) :
    j ∈ positionsWhere p q ↔ ∃ β, p j = some β ∧ q β := by
  classical
  simp [positionsWhere]

@[simp] theorem mem_coloredPositions (p : Fin h → Option Label)
    (color : Label → Bool) (b : Bool) (j : Fin h) :
    j ∈ coloredPositions p color b ↔ ∃ β, p j = some β ∧ color β = b := by
  exact mem_positionsWhere p (fun β => color β = b) j

theorem positionsWhere_true (p : Fin h → Option Label) :
    positionsWhere p (fun _ => True) = regularPositions p := by
  classical
  ext j
  simp only [mem_positionsWhere, mem_regularPositions]
  cases hp : p j <;> simp

theorem positionsWhere_subset_regularPositions (p : Fin h → Option Label)
    (q : Label → Prop) : positionsWhere p q ⊆ regularPositions p := by
  intro j hj
  obtain ⟨β, hβ, _⟩ := (mem_positionsWhere p q j).mp hj
  apply (mem_regularPositions p j).mpr
  rw [hβ]
  exact Option.some_ne_none β

/-- Every subset of the recorded labels has exactly its number of positions.
The hypothesis excludes repetition only for recorded labels; `none` may occur
arbitrarily often. -/
theorem support_filter_card_eq (p : Fin h → Option Label) (hinj : LabelsInjective p)
    (q : Label → Prop) [DecidablePred q] :
    ((support p).filter q).card = (positionsWhere p q).card := by
  classical
  let pos : ∀ β ∈ support p, Fin h := fun β hβ =>
    Classical.choose ((mem_support p β).mp hβ)
  have hpos : ∀ β (hβ : β ∈ support p), p (pos β hβ) = some β := by
    intro β hβ
    exact Classical.choose_spec ((mem_support p β).mp hβ)
  apply Finset.card_bij (fun β hβ => pos β (Finset.mem_filter.mp hβ).1)
  · intro β hβ
    apply (mem_positionsWhere p q _).mpr
    exact ⟨β, hpos β (Finset.mem_filter.mp hβ).1, (Finset.mem_filter.mp hβ).2⟩
  · intro β hβ γ hγ heq
    apply Option.some.inj
    exact (hpos β (Finset.mem_filter.mp hβ).1).symm.trans
      ((congrArg p heq).trans (hpos γ (Finset.mem_filter.mp hγ).1))
  · intro j hj
    obtain ⟨β, hjβ, hqβ⟩ := (mem_positionsWhere p q j).mp hj
    have hβ : β ∈ (support p).filter q :=
      Finset.mem_filter.mpr ⟨(mem_support p β).mpr ⟨j, hjβ⟩, hqβ⟩
    exact ⟨β, hβ, hinj _ _ β (hpos β (Finset.mem_filter.mp hβ).1) hjβ⟩

/-- Distinct recorded labels are in bijection with regular positions. -/
theorem support_card_eq (p : Fin h → Option Label) (hinj : LabelsInjective p) :
    (support p).card = (regularPositions p).card := by
  simpa only [Finset.filter_true, positionsWhere_true] using
    support_filter_card_eq p hinj (fun _ => True)

/-- The bijection also preserves each literal color class. -/
theorem support_color_card_eq (p : Fin h → Option Label) (hinj : LabelsInjective p)
    (color : Label → Bool) (b : Bool) :
    ((support p).filter fun β => color β = b).card =
      (coloredPositions p color b).card :=
  support_filter_card_eq p hinj (fun β => color β = b)

/-- Quarter-balancing the support gives quarter-balancing of regular positions. -/
theorem regular_card_le_four_colored (p : Fin h → Option Label)
    (hinj : LabelsInjective p) (color : Label → Bool) (b : Bool)
    (hbalance : (support p).card ≤ 4 * ((support p).filter fun β => color β = b).card) :
    (regularPositions p).card ≤ 4 * (coloredPositions p color b).card := by
  rw [← support_card_eq p hinj, ← support_color_card_eq p hinj color b]
  exact hbalance

/-- If at least half the positions are regular, each balanced color occupies
at least an eighth of the whole pattern. -/
theorem length_le_eight_colored (p : Fin h → Option Label)
    (hinj : LabelsInjective p) (color : Label → Bool) (b : Bool)
    (hregular : h ≤ 2 * (regularPositions p).card)
    (hbalance : (support p).card ≤ 4 * ((support p).filter fun β => color β = b).card) :
    h ≤ 8 * (coloredPositions p color b).card := by
  calc
    h ≤ 2 * (regularPositions p).card := hregular
    _ ≤ 2 * (4 * (coloredPositions p color b).card) :=
      Nat.mul_le_mul_left 2 (regular_card_le_four_colored p hinj color b hbalance)
    _ = 8 * (coloredPositions p color b).card := by rw [← Nat.mul_assoc]

end QuantitativeVanDerWaerden.RecordedSupport

end OAI
