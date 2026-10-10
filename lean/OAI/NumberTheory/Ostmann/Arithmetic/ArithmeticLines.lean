import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace OAI

/-! # Exact line counts in the ideal giant residues -/

namespace Ostmann

open scoped BigOperators

/-- A feasible line on two unit coordinates has one point for each second coordinate. -/
def unitLineEquiv {G : Type*} [CommGroup G] (a b : G) :
    {xy : G × G // a * xy.1 = b * xy.2} ≃ G where
  toFun xy := xy.1.2
  invFun y := ⟨(a⁻¹ * b * y, y), by simp [mul_assoc]⟩
  left_inv xy := by
    apply Subtype.ext
    apply Prod.ext
    · change a⁻¹ * b * xy.1.2 = xy.1.1
      rw [mul_assoc, ← xy.property]
      simp
    · rfl
  right_inv _ := rfl

theorem card_unitLine {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (a b : G) :
    Fintype.card {xy : G × G // a * xy.1 = b * xy.2} = Fintype.card G :=
  Fintype.card_congr (unitLineEquiv a b)

/-- An external integer coordinate is unrestricted; the second coordinate is still a unit. -/
noncomputable def externalLineEquiv {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (b : ZMod p) :
    {xy : ZMod p × (ZMod p)ˣ // (a : ZMod p) * xy.1 = b * xy.2} ≃ (ZMod p)ˣ where
  toFun xy := xy.1.2
  invFun y := ⟨(b / (a : ZMod p) * y, y), by field_simp⟩
  left_inv xy := by
    apply Subtype.ext
    apply Prod.ext
    · change b / (a : ZMod p) * xy.1.2 = xy.1.1
      apply (mul_left_cancel₀ (Units.ne_zero a))
      calc
        (a : ZMod p) * (b / (a : ZMod p) * xy.1.2) = b * xy.1.2 := by field_simp
        _ = _ := xy.property.symm
    · rfl
  right_inv _ := rfl

theorem card_externalLine {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (b : ZMod p) :
    Fintype.card {xy : ZMod p × (ZMod p)ˣ // (a : ZMod p) * xy.1 = b * xy.2} =
      Fintype.card (ZMod p)ˣ :=
  Fintype.card_congr (externalLineEquiv a b)

theorem unitLine_probability {p : ℕ} [Fact p.Prime] (a b : (ZMod p)ˣ) :
    (Fintype.card {xy : (ZMod p)ˣ × (ZMod p)ˣ // a * xy.1 = b * xy.2} : ℝ) /
      (Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) : ℝ) =
        (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ := by
  rw [card_unitLine, Fintype.card_prod, Nat.cast_mul]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem externalLine_probability {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) (b : ZMod p) :
    (Fintype.card {xy : ZMod p × (ZMod p)ˣ // (a : ZMod p) * xy.1 = b * xy.2} : ℝ) /
      (Fintype.card (ZMod p × (ZMod p)ˣ) : ℝ) = (p : ℝ)⁻¹ := by
  rw [card_externalLine, Fintype.card_prod, ZMod.card, Nat.cast_mul]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem independent_lines_no_unit_solution {K : Type*} [Field K]
    (a b c d x y : K) (hdet : a * d - b * c ≠ 0) (hy : y ≠ 0)
    (h₁ : a * x + b * y = 0) (h₂ : c * x + d * y = 0) : False := by
  have he : (a * d - b * c) * y = 0 := by
    linear_combination a * h₂ - c * h₁
  exact hy ((mul_eq_zero.mp he).resolve_left hdet)

theorem line_zero_first_coefficient {K : Type*} [Field K]
    (b x y : K) (hb : b ≠ 0) (hy : y ≠ 0) : ¬ (0 : K) * x + b * y = 0 := by
  simpa only [zero_mul, zero_add] using mul_ne_zero hb hy

/-- Vanishing two-by-two minors reduce all occurrence tests to one nonzero row. -/
theorem dependent_lines_iff {K I : Type*} [Field K]
    (a b : I → K) (i : I) (ha : a i ≠ 0)
    (hdet : ∀ j, a i * b j - b i * a j = 0) (x y : K) :
    (∀ j, a j * x + b j * y = 0) ↔ a i * x + b i * y = 0 := by
  constructor
  · exact fun h => h i
  · intro h j
    have he : a i * (a j * x + b j * y) = 0 := by
      linear_combination a j * h + y * hdet j
    exact (mul_eq_zero.mp he).resolve_left ha

end Ostmann

end OAI
