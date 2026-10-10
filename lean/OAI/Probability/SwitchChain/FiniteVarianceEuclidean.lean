import OAI.Probability.SwitchChain.FiniteVarianceDecomposition

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteVariance

open FixedBlockMarginal (average)

variable {X I : Type*} [Fintype X] [Fintype I]

theorem average_square_eq_norm_sq_div_card (f : X → ℝ) :
    average (fun x => (f x) ^ 2) =
      ‖WithLp.toLp 2 f‖ ^ 2 / (Fintype.card X : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem variance_eq_centered_norm_sq_div_card (f : X → ℝ) :
    variance f =
      ‖WithLp.toLp 2 (fun x => f x - average f)‖ ^ 2 /
        (Fintype.card X : ℝ) :=
  average_square_eq_norm_sq_div_card _

theorem variance_eq_norm_sq_div_card_of_average_zero
    (f : EuclideanSpace ℝ X) (hf : average (fun x => f x) = 0) :
    variance (fun x => f x) = ‖f‖ ^ 2 / (Fintype.card X : ℝ) := by
  rw [variance_eq_centered_norm_sq_div_card, hf]
  simp only [sub_zero, WithLp.toLp_ofLp]

theorem norm_sum_sq_le_of_variance_bound [Nonempty X]
    (y : I → EuclideanSpace ℝ X) (c : ℝ)
    (hcenter : ∀ i, average (fun x => y i x) = 0)
    (hvar : variance (fun x => ∑ i, y i x) ≤
      c * ∑ i, variance (fun x => y i x)) :
    ‖∑ i, y i‖ ^ 2 ≤ c * ∑ i, ‖y i‖ ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card X := by
    exact_mod_cast Fintype.card_pos
  have hsum : average (fun x => (∑ i, y i) x) = 0 := by
    simp only [WithLp.ofLp_sum, Finset.sum_apply, average_sum, hcenter, Finset.sum_const_zero]
  have hleft := variance_eq_norm_sq_div_card_of_average_zero (∑ i, y i) hsum
  have hright (i : I) := variance_eq_norm_sq_div_card_of_average_zero (y i) (hcenter i)
  simp only [WithLp.ofLp_sum, Finset.sum_apply] at hleft
  rw [hleft] at hvar
  simp_rw [hright] at hvar
  rw [← Finset.sum_div, ← mul_div_assoc] at hvar
  exact (div_le_div_iff_of_pos_right hcard).mp hvar

end Problem315.FiniteVariance

end

end OAI
