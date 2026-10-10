import OAI.Analysis.MarkovType.CoefficientBlockGain
import OAI.Analysis.MarkovType.TriangularQuotient

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem FiniteTriangularObstruction.coefficient_half_gain_quotients
    (hX : FiniteTriangularObstruction X) {K : ℝ} (hK : 1 < K) :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (F : Submodule ℝ X) [IsClosed (F : Set X)] (x : Fin M → X ⧸ F),
        CoefficientBasic K x →
          ∃ i : Fin M, ‖x i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, x j‖ := by
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  let θ : ℝ := 1 / (4 * K ^ 2)
  have hden : 0 < 4 * K ^ 2 := by positivity
  have hθpos : 0 < θ := one_div_pos.mpr hden
  have hθlt : θ < 1 := by
    apply (div_lt_one hden).mpr
    nlinarith
  obtain ⟨n, hn, hnone⟩ := hX (θ / 2) (div_pos hθpos (by norm_num)) (by linarith)
  let M := max n 2
  have hM : 0 < M := lt_of_lt_of_le (by decide : 0 < 2) (le_max_right n 2)
  have hnoneM : ¬ Nonempty (TriangularSystem X M (θ / 2)) :=
    TriangularSystem.no_longer_of_no_shorter (le_max_left n 2) hnone
  refine ⟨M, le_max_right n 2, ?_⟩
  intro F _ x hx
  exact hx.exists_half_entry_of_no_triangular hKpos hM
    (no_triangular_quotient_of_no_triangular hnoneM F)

end MarkovSuperreflexivity

end OAI
