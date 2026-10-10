import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# The exact positive constant in the finite boundary obstruction

The energy inequality is rearranged only after proving the denominators
positive. No sign condition is imposed on a correlation or on its error bound.
The choice of the integer parameter is independent of the finite group set.
-/

namespace ThompsonNonamenability

noncomputable def boundaryConstant (L δ : ℝ) (D : ℕ) : ℝ :=
  (δ ^ 2 / L ^ 2 - 4 / (D : ℝ)) / (4 * (1 - 1 / (D : ℝ)))

theorem boundary_denominator_pos {D : ℕ} (hD : 2 ≤ D) :
    0 < 4 * (1 - 1 / (D : ℝ)) := by
  have htwo : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hpos : (0 : ℝ) < (D : ℝ) := by linarith
  have hinv : 1 / (D : ℝ) < 1 := (div_lt_one hpos).2 (by linarith)
  linarith

theorem boundary_numerator_pos {L δ : ℝ} {D : ℕ}
    (hL : 0 < L) (hδ : 0 < δ) (hD : 2 ≤ D)
    (hlarge : 4 * L ^ 2 / δ ^ 2 < (D : ℝ)) :
    0 < δ ^ 2 / L ^ 2 - 4 / (D : ℝ) := by
  have hLp : 0 < L ^ 2 := sq_pos_of_pos hL
  have hδp : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hDp : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hD)
  have hcross : 4 * L ^ 2 < (D : ℝ) * δ ^ 2 :=
    (div_lt_iff₀ hδp).1 hlarge
  have hratio : 4 / (D : ℝ) < δ ^ 2 / L ^ 2 :=
    (div_lt_div_iff₀ hDp hLp).2 (by nlinarith [hcross])
  exact sub_pos.mpr hratio

theorem boundaryConstant_pos {L δ : ℝ} {D : ℕ}
    (hL : 0 < L) (hδ : 0 < δ) (hD : 2 ≤ D)
    (hlarge : 4 * L ^ 2 / δ ^ 2 < (D : ℝ)) :
    0 < boundaryConstant L δ D := by
  unfold boundaryConstant
  exact div_pos (boundary_numerator_pos hL hδ hD hlarge)
    (boundary_denominator_pos hD)

/-- Algebraic consequence of the genuine finite energy estimate. -/
theorem boundaryConstant_le_of_energy {L δ η : ℝ} {D : ℕ}
    (hL : 0 < L) (hD : 2 ≤ D)
    (henergy : δ ^ 2 ≤ L ^ 2 *
      (4 / (D : ℝ) + 4 * (1 - 1 / (D : ℝ)) * η)) :
    boundaryConstant L δ D ≤ η := by
  have hLp : 0 < L ^ 2 := sq_pos_of_pos hL
  have hdivide : δ ^ 2 / L ^ 2 ≤
      4 / (D : ℝ) + 4 * (1 - 1 / (D : ℝ)) * η := by
    apply (div_le_iff₀ hLp).2
    nlinarith [henergy]
  unfold boundaryConstant
  apply (div_le_iff₀ (boundary_denominator_pos hD)).2
  nlinarith [hdivide]

/-- Choose the finite branching parameter before choosing any finite group set. -/
theorem exists_branching_parameter (L δ : ℝ) :
    ∃ D : ℕ, 2 ≤ D ∧ 4 * L ^ 2 / δ ^ 2 < (D : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * L ^ 2 / δ ^ 2)
  refine ⟨max 2 n, le_max_left _ _, lt_of_lt_of_le hn ?_⟩
  exact_mod_cast (le_max_right 2 n)

end ThompsonNonamenability

end OAI
