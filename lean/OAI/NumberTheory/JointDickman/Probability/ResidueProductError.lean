import OAI.NumberTheory.JointDickman.Probability.HistogramResidueProjection

namespace OAI

/-! # Passing residue square errors through the two-endpoint product -/

namespace JointDickman
open Finset

theorem restricted_residue_product_error {ι : Type*} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] (A B C D : ι → ℂ) :
    ‖∑ r, if P r then A r*B r-C r*D r else 0‖ ≤
      Real.sqrt (∑ r, ‖A r-C r‖^2)*Real.sqrt (∑ r, ‖B r‖^2)+
        Real.sqrt (∑ r, ‖C r‖^2)*Real.sqrt (∑ r, ‖B r-D r‖^2) := by
  classical
  have hp (r : ι) : ‖A r*B r-C r*D r‖ ≤
      ‖A r-C r‖*‖B r‖+‖C r‖*‖B r-D r‖ := by
    calc
      _ = ‖(A r-C r)*B r+C r*(B r-D r)‖ := by congr 1; ring
      _ ≤ ‖(A r-C r)*B r‖+‖C r*(B r-D r)‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul,norm_mul]
  calc
    _ ≤ ∑ r, ‖if P r then A r*B r-C r*D r else 0‖ := norm_sum_le _ _
    _ ≤ ∑ r, (‖A r-C r‖*‖B r‖+‖C r‖*‖B r-D r‖) := by
      apply sum_le_sum
      intro r _
      split_ifs
      · exact hp r
      · simpa using add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ r, ‖A r-C r‖*‖B r‖)+(∑ r, ‖C r‖*‖B r-D r‖) := sum_add_distrib
    _ ≤ _ := add_le_add (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
      (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

theorem restricted_residue_product_error_bound {ι : Type*} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] (A B C D : ι → ℂ)
    {e₁ e₂ u v : ℝ}
    (h₁ : (∑ r, ‖A r-C r‖^2) ≤ e₁) (h₂ : (∑ r, ‖B r-D r‖^2) ≤ e₂)
    (hC : (∑ r, ‖C r‖^2) ≤ u) (hB : (∑ r, ‖B r‖^2) ≤ v) :
    ‖∑ r, if P r then A r*B r-C r*D r else 0‖ ≤
      Real.sqrt e₁*Real.sqrt v+Real.sqrt u*Real.sqrt e₂ := by
  refine (restricted_residue_product_error P A B C D).trans ?_
  apply add_le_add
  · exact mul_le_mul (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt hB)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · exact mul_le_mul (Real.sqrt_le_sqrt hC) (Real.sqrt_le_sqrt h₂)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end JointDickman

end OAI
