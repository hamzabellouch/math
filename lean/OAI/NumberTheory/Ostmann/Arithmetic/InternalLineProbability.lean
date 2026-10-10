import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLines

namespace OAI

/-! # Exact rank and feasibility tests for repeated internal-prime occurrences

Section 8, equation `arith-line-probabilities`: the simultaneous linear tests
have probability zero in rank two, and exactly `1/(p-1)` or `1/p` in the
respective feasible rank-one cases. A distinguished nonzero occurrence is
sufficient; no independence of the repeated tests is assumed.
-/

namespace Ostmann

open scoped BigOperators
open scoped Classical

def lineRankOne {K I : Type*} [CommRing K] (a b : I → K) (i : I) : Prop :=
  ∀ j, a i * b j - b i * a j = 0

def externalLineFeasible {K I : Type*} [CommRing K] (a b : I → K) (i : I) : Prop :=
  a i ≠ 0 ∧ lineRankOne a b i

def unitLineFeasible {K I : Type*} [CommRing K] (a b : I → K) (i : I) : Prop :=
  a i ≠ 0 ∧ b i ≠ 0 ∧ lineRankOne a b i

theorem lineSystem_iff {K I : Type*} [Field K] (a b : I → K) (i : I)
    (hrow : a i ≠ 0 ∨ b i ≠ 0) (x y : K) (hy : y ≠ 0) :
    (∀ j, a j * x + b j * y = 0) ↔
      externalLineFeasible a b i ∧ a i * x + b i * y = 0 := by
  constructor
  · intro h
    have ha : a i ≠ 0 := by
      intro ha
      exact line_zero_first_coefficient (b i) x y
        (hrow.resolve_left (not_not.mpr ha)) hy (ha ▸ h i)
    refine ⟨⟨ha, fun j => ?_⟩, h i⟩
    have he : (a i * b j - b i * a j) * y = 0 := by
      linear_combination a i * h j - a j * h i
    exact (mul_eq_zero.mp he).resolve_right hy
  · rintro ⟨⟨ha, hrank⟩, h⟩
    exact (dependent_lines_iff a b i ha hrank x y).mpr h

theorem unit_lineSystem_iff {K I : Type*} [Field K] (a b : I → K) (i : I)
    (hrow : a i ≠ 0 ∨ b i ≠ 0) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (∀ j, a j * x + b j * y = 0) ↔
      unitLineFeasible a b i ∧ a i * x + b i * y = 0 := by
  rw [lineSystem_iff a b i hrow x y hy]
  constructor
  · rintro ⟨⟨ha, hrank⟩, h⟩
    have hb : b i ≠ 0 := by
      intro hb
      have he : a i * x = 0 := by simpa only [hb, zero_mul, add_zero] using h
      exact mul_ne_zero ha hx he
    exact ⟨⟨ha, hb, hrank⟩, h⟩
  · exact fun ⟨⟨ha, _, hrank⟩, h⟩ => ⟨⟨ha, hrank⟩, h⟩

theorem external_lineSystem_probability {I : Type*} {p : ℕ} [Fact p.Prime]
    (a b : I → ZMod p) (i : I) (hrow : a i ≠ 0 ∨ b i ≠ 0) :
    (Fintype.card {z : ZMod p × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} : ℝ) /
      Fintype.card (ZMod p × (ZMod p)ˣ) =
      if externalLineFeasible a b i then (p : ℝ)⁻¹ else 0 := by
  classical
  by_cases hg : externalLineFeasible a b i
  · rw [ite_eq_left hg]
    let u : (ZMod p)ˣ := (isUnit_iff_ne_zero.mpr hg.1).unit
    have hu : (u : ZMod p) = a i := IsUnit.unit_spec _
    have he (z : ZMod p × (ZMod p)ˣ) :
        (∀ j, a j * z.1 + b j * z.2 = 0) ↔ (u : ZMod p) * z.1 = (-b i) * z.2 := by
      rw [lineSystem_iff a b i hrow z.1 z.2 (Units.ne_zero z.2), and_iff_right hg, hu]
      constructor <;> intro h <;> linear_combination h
    rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
    exact externalLine_probability u (-b i)
  · rw [ite_eq_right hg]
    have : IsEmpty {z : ZMod p × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} :=
      ⟨fun z => hg ((lineSystem_iff a b i hrow z.1.1 z.1.2
        (Units.ne_zero z.1.2)).mp z.2).1⟩
    simp

theorem unit_lineSystem_probability {I : Type*} {p : ℕ} [Fact p.Prime]
    (a b : I → ZMod p) (i : I) (hrow : a i ≠ 0 ∨ b i ≠ 0) :
    (Fintype.card {z : (ZMod p)ˣ × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} : ℝ) /
      Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) =
      if unitLineFeasible a b i then (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ else 0 := by
  classical
  by_cases hg : unitLineFeasible a b i
  · rw [ite_eq_left hg]
    let u : (ZMod p)ˣ := (isUnit_iff_ne_zero.mpr hg.1).unit
    let v : (ZMod p)ˣ := (isUnit_iff_ne_zero.mpr hg.2.1).unit
    have hu : (u : ZMod p) = a i := IsUnit.unit_spec _
    have hv : (v : ZMod p) = b i := IsUnit.unit_spec _
    have he (z : (ZMod p)ˣ × (ZMod p)ˣ) :
        (∀ j, a j * z.1 + b j * z.2 = 0) ↔ u * z.1 = (-v) * z.2 := by
      rw [unit_lineSystem_iff a b i hrow z.1 z.2 (Units.ne_zero z.1) (Units.ne_zero z.2),
        and_iff_right hg]
      rw [← Units.val_inj]
      simp only [Units.val_mul, Units.val_neg, hu, hv]
      constructor <;> intro h <;> linear_combination h
    rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
    exact unitLine_probability u (-v)
  · rw [ite_eq_right hg]
    have : IsEmpty {z : (ZMod p)ˣ × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} :=
      ⟨fun z => hg ((unit_lineSystem_iff a b i hrow z.1.1 z.1.2
        (Units.ne_zero z.1.1) (Units.ne_zero z.1.2)).mp z.2).1⟩
    simp

end Ostmann

end OAI
