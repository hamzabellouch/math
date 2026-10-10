import Mathlib.Tactic

namespace OAI

/-!
# Arithmetic of the terminal path-system classification

These are the numerical steps in manuscript Lemmas `terminal:increment`
and `terminal:classification`. They do not assume any graph conclusion.
-/

namespace CycleClique.Construction
/-- The concavity calculation in `terminal:increment`, checked in each of
the five possible integral cases of its excess `j`. -/
theorem terminal_increment_arithmetic {t k r j : ℕ}
    (ht : 9 ≤ t) (hk : k ≤ 2 * t + 1) (htk : t ≤ k)
    (hj : 1 ≤ j) (hj' : j ≤ 5) (hr : t + 1 ≤ 2 * r + j) :
    ¬ ((r - 1) * (j + 2) ≤ k - t) := by
  interval_cases j <;> omega

/-- The three numerical alternatives that survive equation
`terminal:arithmetic`, including all ceiling/parity restrictions. -/
theorem terminal_classification_arithmetic {k t L e v d : ℕ}
    (ht : 9 ≤ t) (htk : t ≤ k) (hk : k ≤ 2 * t + 1)
    (hL : L = k - t) (hd : 2 ≤ d) (hd' : d ≤ 6)
    (hde : d * e ≤ L) (htv : t ≤ v + d) (hve : v ≤ 2 * e) :
    (d = 2 ∧ t ≤ v + 2) ∨
    (d = 3 ∧ (t = 9 ∨ t = 11) ∧ 2 * e = t - 3 ∧ v = t - 3) ∨
    (d = 5 ∧ t = 9 ∧ k = 19 ∧ e = 2 ∧ v = 4) := by
  interval_cases d <;> omega

end CycleClique.Construction

end OAI
