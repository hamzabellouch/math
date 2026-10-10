import OAI.Analysis.KadisonKastler.CompletelyBounded
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

namespace OAI

/-! # Extending the unitary commutator estimate to the whole algebra -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A V : Type*} [CStarAlgebra A]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The four-unitary decomposition loses only a factor of two when
extending a linear norm estimate from unitaries to arbitrary elements. -/
theorem linear_norm_le_twice_unitary_bound (F : A →ₗ[ℂ] V) {C : ℝ}
    (hF : ∀ u : unitary A, ‖F (u : A)‖ ≤ C) (x : A) :
    ‖F x‖ ≤ 2 * C * ‖x‖ := by
  obtain ⟨u, c, hx, hc⟩ := CStarAlgebra.exists_sum_four_unitary x
  conv_lhs => rw [hx, map_sum]
  calc
    _ ≤ ∑ i : Fin 4, ‖F (c i • (u i : A))‖ := norm_sum_le _ _
    _ = ∑ i : Fin 4, ‖c i‖ * ‖F (u i : A)‖ := by simp only [map_smul, norm_smul]
    _ ≤ ∑ _ : Fin 4, (‖x‖ / 2) * C := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (hc i) (hF (u i)) (norm_nonneg _) (by positivity)
    _ = 2 * C * ‖x‖ := by simp; ring

/-- The numerical final step of the amplification argument. -/
theorem linear_norm_le_five_sixty_four (F : A →ₗ[ℂ] V) {δ : ℝ}
    (hF : ∀ u : unitary A, ‖F (u : A)‖ ≤ 282 * δ) (x : A) :
    ‖F x‖ ≤ 564 * δ * ‖x‖ := by
  have h := linear_norm_le_twice_unitary_bound F hF x
  convert h using 1
  ring

/-- The manuscript uses the round universal constant 600. -/
theorem linear_norm_le_six_hundred (F : A →ₗ[ℂ] V) {δ : ℝ}
    (hδ : 0 ≤ δ) (hF : ∀ u : unitary A, ‖F (u : A)‖ ≤ 282 * δ) (x : A) :
    ‖F x‖ ≤ 600 * δ * ‖x‖ := by
  apply (linear_norm_le_five_sixty_four F hF x).trans
  have hn := norm_nonneg x
  nlinarith

end

end KadisonKastler

end OAI
