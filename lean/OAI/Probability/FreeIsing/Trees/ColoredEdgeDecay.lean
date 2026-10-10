import OAI.Probability.FreeIsing.Estimates.NonbacktrackingDecay
import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic
import OAI.Probability.FreeIsing.Trees.ColoredEdgeLifts

namespace OAI

noncomputable section

namespace Problem367.ColoredEdgeLifts
open NonbacktrackingComplement

lemma degree_decay_parameters {d : ℕ} (hd : 3 ≤ d) :
    let q := (Real.sqrt ((d : ℝ) - 1))⁻¹
    0 < q ∧ q < 1 ∧ q ^ 2 = ((d : ℝ) - 1)⁻¹ ∧
      1 + q ^ 2 = (d : ℝ) * ((d : ℝ) - 1)⁻¹ ∧
      vertexRate q = 2 * Real.sqrt ((d : ℝ) - 1) / d := by
  dsimp only
  have hb := branching_pos hd
  have hs := threshold_sqrt_pos hd
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 := Real.sq_sqrt hb.le
  have hs1 : 1 < Real.sqrt ((d : ℝ) - 1) := by nlinarith
  have hq2 : (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ 2 = ((d : ℝ) - 1)⁻¹ := by
    rw [inv_pow, hs2]
  refine ⟨inv_pos.mpr hs, (inv_lt_one₀ hs).mpr hs1, hq2, ?_, ?_⟩
  · rw [hq2]
    field_simp
    ring
  · unfold vertexRate
    rw [hq2]
    field_simp
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_forwardOperator_pow_bound {d : ℕ} (hd : 3 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (hS : ∀ i, Function.Involutive (S i))
    (hA : ‖neighborAverage S‖ ≤ 2 * Real.sqrt ((d : ℝ) - 1) / d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n‖ ≤
        K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n := by
  obtain ⟨hq, hq1, hq2, hc, hρ⟩ := degree_decay_parameters hd
  have hnorm : ‖neighborAverage S‖ ≤ vertexRate (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    rw [hρ]
    exact hA
  have hh := exists_norm_edgeOperator_pow_bound_real (E := E) (V := EdgeSpace d E) hq hq1
    (tailLift (𝕜 := ℝ) (by omega : 0 < d)) (headLift (by omega : 0 < d) S)
    (reversal S) (neighborAverage S) (neighborAverage_selfAdjoint S hS) hnorm
    (tailLift_adjoint_head_eq_average (by omega : 0 < d) S)
    (reversal_tail (by omega : 0 < d) S) (reversal_head (by omega : 0 < d) S hS)
  rw [hc, hq2] at hh
  exact hh

theorem summable_norm_forwardOperator_pow {d : ℕ} (hd : 3 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (hS : ∀ i, Function.Involutive (S i))
    (hA : ‖neighborAverage S‖ ≤ 2 * Real.sqrt ((d : ℝ) - 1) / d) :
    Summable (fun n : ℕ => ‖forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n‖) := by
  obtain ⟨hq, hq1, _, _, _⟩ := degree_decay_parameters hd
  obtain ⟨K, _, hK⟩ := exists_forwardOperator_pow_bound hd S hS hA
  exact summable_norm_of_affine_geometric_bound (F := EdgeSpace d E →L[ℝ] EdgeSpace d E) _ K _ hq.le hq1 hK

end Problem367.ColoredEdgeLifts

end

end OAI
