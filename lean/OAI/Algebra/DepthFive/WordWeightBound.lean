import OAI.Algebra.DepthFive.WordWeightParameters
import OAI.Algebra.DepthFive.WordSum
import OAI.Algebra.DepthFive.RunLayerWeights

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.LowerParameters

/-- The actual rounded parameters discharge every numerical and run-product
premise of the corrected word sum. Only the chosen schedule remains an input. -/
theorem sum_actual_weight_le_exp_of_parameters {n : ℕ} (hn : 16 ≤ n + 1)
    (edges : Finset (Fin (n + 1) × Fin (n + 1)))
    (V S : Finset (Fin (n + 1))) (R : Fin (n + 1) → Fin (n + 1) → Prop)
    (hS : S ⊆ V) (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    (hswitch : ∀ w, SwitchRestoration.switchCount edges w = (WordSwitches.switches w).card)
    (hend : (V \ S).card ≤ 1)
    (hcard : 2 * (V.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    (hdiscrepancy : ∀ l : List (Fin (n + 1)), l <:+: List.ofFn id →
      (l.countP (fun i => decide (i ∈ V)) : ℝ) -
        rho (n + 1) * l.countP (fun i => !decide (i ∈ V)) ≤ 1 + rho (n + 1)) :
    (∑ w, IsolatedWeight.weight edges V R
      (alpha (n + 1))⁻¹ (beta (n + 1)) (((n + 1 : ℕ) : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  have hn4 : 4 ≤ n + 1 := by omega
  apply WordSum.sum_actual_weight_le_exp_of_endpoints n
    (alpha (n + 1))⁻¹ (beta (n + 1))
    ((2 / (b (n + 1) : ℝ)) * ((n + 1 : ℕ) : ℝ))
    edges V S R hS hV hR hdegree hswitch hend hcard
    (one_le_inv_alpha hn4) (inv_alpha_le_sqrt hn4) (beta_pos hn4).le
    (word_error_mul_n_le_sqrt hn)
  intro w
  exact RunLayerWeights.count_weight_le_exp_mul_runCount w V
    (alpha_pos hn4) (alpha_lt_one hn4).le (beta_pos hn4).le
    (by positivity) (beta_le_rpow_mul_exp_two_div hn)
    (alpha_run_scale_le hn4) hdiscrepancy

end Problem335.LowerParameters

end

end OAI
