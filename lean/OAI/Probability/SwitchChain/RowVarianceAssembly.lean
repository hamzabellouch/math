import OAI.Probability.SwitchChain.TripleProjectionBridge

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.RowVarianceAssembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sq_eq_parts (C : E →ₗ[ℝ] E)
    (hsymm : C.IsSymmetric) (hidem : ∀ x, C (C x) = C x) (x : E) :
    ‖x‖ ^ 2 = ‖x - C x‖ ^ 2 + ‖C x‖ ^ 2 := by
  have hi := hsymm x (C x)
  rw [hidem, real_inner_self_eq_norm_sq] at hi
  rw [norm_sub_sq_real]
  linarith

theorem norm_sum_sq_le_of_projection_parts {ι : Type*} [Fintype ι]
    (C : E →ₗ[ℝ] E)
    (hsymm : C.IsSymmetric) (hidem : ∀ x, C (C x) = C x)
    (y : ι → E) (c : ℝ)
    (hcenter : ‖∑ i, (y i - C (y i))‖ ^ 2 ≤
      c * ∑ i, ‖y i - C (y i)‖ ^ 2)
    (hmean : ‖∑ i, C (y i)‖ ^ 2 ≤ c * ∑ i, ‖C (y i)‖ ^ 2) :
    ‖∑ i, y i‖ ^ 2 ≤ c * ∑ i, ‖y i‖ ^ 2 := by
  have htotal := norm_sq_eq_parts C hsymm hidem (∑ i, y i)
  rw [map_sum, ← Finset.sum_sub_distrib] at htotal
  have hparts : (∑ i, ‖y i‖ ^ 2) =
      (∑ i, ‖y i - C (y i)‖ ^ 2) + ∑ i, ‖C (y i)‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => norm_sq_eq_parts C hsymm hidem (y i))
  rw [hparts]
  nlinarith

theorem three_row_variance_of_conditional_bounds
    (C : E →ₗ[ℝ] E)
    (hsymm : C.IsSymmetric) (hidem : ∀ x, C (C x) = C x)
    (y : Fin 3 → E)
    (hfixed : ‖∑ i, (y i - C (y i))‖ ^ 2 ≤
      2 * ∑ i, ‖y i - C (y i)‖ ^ 2)
    (hcounts : ‖∑ i, C (y i)‖ ^ 2 ≤ 2 * ∑ i, ‖C (y i)‖ ^ 2) :
    ‖∑ i, y i‖ ^ 2 ≤ 2 * ∑ i, ‖y i‖ ^ 2 :=
  norm_sum_sq_le_of_projection_parts C hsymm hidem y 2 hfixed hcounts

theorem triple_square_of_two_conditional_bounds
    (P : Fin 3 → E →ₗ[ℝ] E) (C : E → E) (K : E →ₗ[ℝ] E)
    (hPsymm : ∀ i, (P i).IsSymmetric)
    (hPidem : ∀ i x, P i (P i x) = P i x)
    (hPfix : ∀ i x, P i (C x) = C x)
    (hKsymm : K.IsSymmetric) (hKidem : ∀ x, K (K x) = K x)
    (hfixed : ∀ x,
      ‖∑ i, (P i (x - C x) - K (P i (x - C x)))‖ ^ 2 ≤
        2 * ∑ i, ‖P i (x - C x) - K (P i (x - C x))‖ ^ 2)
    (hcounts : ∀ x, ‖∑ i, K (P i (x - C x))‖ ^ 2 ≤
      2 * ∑ i, ‖K (P i (x - C x))‖ ^ 2) :
    ∀ x, ⟪x, ∑ i, (x - P i x)⟫ ≤ ‖∑ i, (x - P i x)‖ ^ 2 := by
  apply TripleProjectionBridge.triple_square_of_centered_row_variance
    P C hPsymm hPidem hPfix
  intro x
  exact three_row_variance_of_conditional_bounds K hKsymm hKidem
    (fun i => P i (x - C x)) (hfixed x) (hcounts x)

end Problem315.RowVarianceAssembly

end

end OAI
