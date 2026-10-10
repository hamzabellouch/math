import Mathlib

namespace OAI

/-!
# Localization of the four body modes

The arithmetic case analysis assumes the stated order inequalities and entry
values, independently of the host-position encoding.
-/

namespace Problem348.ModeLocalization

/-- The four entries of the body pattern, in row-major order. -/
def IsP (a b c d : Bool) : Prop :=
  a = true ∧ b = false ∧ c = true ∧ d = true

/-- Within either parity class, taking the parent preserves and reflects order. -/
theorem le_iff_parent_le_of_same_parity {p q : ℕ}
    (hparity : p % 2 = q % 2) :
    p ≤ q ↔ p / 2 ≤ q / 2 := by
  omega

theorem eq_of_parent_eq_of_same_parity {p q : ℕ}
    (hparity : p % 2 = q % 2) (hparent : p / 2 = q / 2) : p = q := by
  omega

/-- A `V_i^+` body cannot match `P`: its row order forces the zero to be one. -/
theorem vPlus_not_isP (p a b : ℕ) (horder : p / 2 ≤ a) :
    ¬ IsP true (decide (p / 2 ≤ b)) true (decide (a ≤ b)) := by
  simp only [IsP, true_and, decide_eq_false_iff_not, decide_eq_true_eq]
  omega

/-- A `V_i^-` body cannot match `P`: its row order forces the last one to be zero. -/
theorem vMinus_not_isP (p a b : ℕ) (horder : a ≤ p / 2) :
    ¬ IsP true (decide (a < b)) true (decide (p / 2 < b)) := by
  simp only [IsP, true_and, decide_eq_false_iff_not, decide_eq_true_eq]
  omega

/-- A `W_{i,d}^+` body cannot match `P`, including at the shared leaf level. -/
theorem wPlus_not_isP (p q b : ℕ) (horder : b ≤ q / 2)
    (hparity : p % 2 = q % 2) :
    ¬ IsP (decide (p / 2 ≤ b)) (decide (p ≤ q)) true true := by
  simp only [IsP, and_true, decide_eq_false_iff_not, decide_eq_true_eq]
  omega

/-- In a minus `W` mode, a body match can occur only on a shared leaf diagonal. -/
theorem wMinus_isP_implies_leaf_diagonal
    (h i p q b : ℕ) (horder : q / 2 ≤ b)
    (hparity : p % 2 = q % 2)
    (hbody : IsP (if i = h then decide (p ≤ q) else decide (p < q))
      (decide (p / 2 < b)) true true) :
    i = h ∧ p = q := by
  by_cases hleaf : i = h
  · simp only [hleaf, ite_true, IsP, and_true,
      decide_eq_false_iff_not, decide_eq_true_eq] at hbody
    constructor
    · exact hleaf
    · omega
  · simp only [hleaf, ite_false, IsP, and_true,
      decide_eq_false_iff_not, decide_eq_true_eq] at hbody
    omega

/-- Conversely, the diagonal leaf choice with its parent column gives `P`. -/
theorem wMinus_leaf_diagonal_isP (h p : ℕ) :
    IsP (if h = h then decide (p ≤ p) else decide (p < p))
      (decide (p / 2 < p / 2)) true true := by
  simp [IsP]

end Problem348.ModeLocalization

end OAI
