import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Extending estimates from unitaries

The final step of the uniform amplification argument bounds a linear
commutator map on every contraction from its bound on unitaries.  This
uses the four-unitary decomposition already proved in Mathlib.
-/

namespace KadisonKastler

variable {A B : Type*} [CStarAlgebra A] [NormedAddCommGroup B] [NormedSpace ℂ B]

/-- A uniform estimate on unitaries extends to the whole algebra with a
factor of two. Continuity need not be assumed for this pointwise statement. -/
theorem norm_le_twice_unitary_bound (T : A →ₗ[ℂ] B) {C : ℝ}
    (hT : ∀ u : unitary A, ‖T (u : A)‖ ≤ C) (x : A) :
    ‖T x‖ ≤ 2 * C * ‖x‖ := by
  obtain ⟨u, c, hx, hc⟩ := CStarAlgebra.exists_sum_four_unitary x
  calc
    ‖T x‖ = ‖∑ i : Fin 4, c i • T (u i : A)‖ := by rw [hx, map_sum]; simp only [map_smul]
    _ ≤ ∑ i : Fin 4, ‖c i • T (u i : A)‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin 4, ‖c i‖ * ‖T (u i : A)‖ := by simp only [norm_smul]
    _ ≤ ∑ _i : Fin 4, (‖x‖ / 2) * C := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (hc i) (hT (u i)) (norm_nonneg _) (by positivity)
    _ = 2 * C * ‖x‖ := by simp; ring

/-- The operator-norm form of the extension from unitaries. -/
theorem opNorm_le_twice_unitary_bound (T : A →L[ℂ] B) {C : ℝ}
    (hT : ∀ u : unitary A, ‖T (u : A)‖ ≤ C) : ‖T‖ ≤ 2 * C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hT 1)
  apply T.opNorm_le_bound (mul_nonneg (by norm_num) hC)
  exact norm_le_twice_unitary_bound T.toLinearMap hT

/-- The numerical constants used at the end of the manuscript's
amplification proof: a unitary bound of `282 δ` gives `564 δ`. -/
theorem norm_le_amplification_bound (T : A →ₗ[ℂ] B) {δ : ℝ}
    (hT : ∀ u : unitary A, ‖T (u : A)‖ ≤ 282 * δ) (x : A) :
    ‖T x‖ ≤ 564 * δ * ‖x‖ := by
  have h := norm_le_twice_unitary_bound T hT x
  convert h using 1
  ring

end KadisonKastler

end OAI
