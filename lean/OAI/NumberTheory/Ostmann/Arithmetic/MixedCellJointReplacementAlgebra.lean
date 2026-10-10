import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellJointReplacementPrior

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.MixedCellJointReplacement
open scoped BigOperators

theorem mixed_sum_error {α β : Type*} [Fintype α] [Fintype β]
    (μ : α → ℝ) (J : ℝ) (X : α → ℂ) (P : ℂ) (F : α → β → ℂ)
    {E Q B : ℝ} (hE : 0 ≤ E) (_hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hμ : ∀ r, |μ r-J| ≤ E) (hP : ‖P‖ ≤ B)
    (hX : ∀ r, ‖X r-P*(∑ u, F r u)‖ ≤ Q*(∑ u, ‖F r u‖)) :
    ‖(∑ r, (μ r : ℂ)*X r)-(J : ℂ)*P*(∑ r, ∑ u, F r u)‖ ≤
      (E*B+(|J|+E)*Q)*(∑ r, ∑ u, ‖F r u‖) := by
  have hm (r : α) : ‖(μ r : ℂ)‖ ≤ |J|+E := by
    have h := abs_add_le (μ r-J) J
    rw [sub_add_cancel] at h
    simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith [hμ r]
  have hd (r : α) : ‖(μ r : ℂ)-(J : ℂ)‖ ≤ E := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hμ r
  have hp (r : α) : ‖(μ r : ℂ)*X r-(J : ℂ)*P*(∑ u, F r u)‖ ≤
      (E*B+(|J|+E)*Q)*(∑ u, ‖F r u‖) := by
    have he : (μ r : ℂ)*X r-(J : ℂ)*P*(∑ u, F r u) =
      (μ r : ℂ)*(X r-P*(∑ u, F r u))+
        ((μ r : ℂ)-(J : ℂ))*P*(∑ u, F r u) := by ring
    rw [he]
    calc
      _ ≤ ‖(μ r : ℂ)*(X r-P*(∑ u, F r u))‖+
          ‖((μ r : ℂ)-(J : ℂ))*P*(∑ u, F r u)‖ := norm_add_le _ _
      _ = ‖(μ r : ℂ)‖*‖X r-P*(∑ u, F r u)‖+
          ‖(μ r : ℂ)-(J : ℂ)‖*‖P‖*‖∑ u, F r u‖ := by simp only [norm_mul]
      _ ≤ (|J|+E)*(Q*(∑ u, ‖F r u‖))+E*B*(∑ u, ‖F r u‖) := by
        apply add_le_add
        · exact mul_le_mul (hm r) (hX r) (norm_nonneg _) (by positivity)
        · exact mul_le_mul (mul_le_mul (hd r) hP (norm_nonneg _) hE)
            (norm_sum_le _ _) (norm_nonneg _) (mul_nonneg hE hB)
      _ = _ := by ring
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r, ‖(μ r : ℂ)*X r-(J : ℂ)*P*(∑ u, F r u)‖ := norm_sum_le _ _
    _ ≤ ∑ r, (E*B+(|J|+E)*Q)*(∑ u, ‖F r u‖) := Finset.sum_le_sum (fun r _ => hp r)
    _ = _ := (Finset.mul_sum _ _ _).symm

end Ostmann.Arithmetic.MixedCellJointReplacement
end

end OAI
