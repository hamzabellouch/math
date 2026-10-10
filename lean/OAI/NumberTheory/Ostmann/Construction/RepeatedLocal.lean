import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem pointwise_norm_le_sqrt_card {ι : Type*} [Fintype ι]
    (f : ι → ℂ) (hf : (∑ x, ‖f x‖^2) ≤ Fintype.card ι) (x : ι) :
    ‖f x‖ ≤ Real.sqrt (Fintype.card ι) := by
  apply (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)).mpr
  exact (Finset.single_le_sum (fun y _ => sq_nonneg ‖f y‖) (Finset.mem_univ x)).trans hf

theorem two_local_abs_sum_le {ι : Type*} [Fintype ι]
    (f g : ι → ℂ) (hf : (∑ x, ‖f x‖^2) ≤ Fintype.card ι)
    (hg : (∑ x, ‖g x‖^2) ≤ Fintype.card ι) :
    (∑ x, ‖f x‖*‖g x‖) ≤ Fintype.card ι := by
  calc
    _ ≤ Real.sqrt (∑ x, ‖f x‖^2)*Real.sqrt (∑ x, ‖g x‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ ≤ Real.sqrt (Fintype.card ι)*Real.sqrt (Fintype.card ι) :=
      mul_le_mul (Real.sqrt_le_sqrt hf) (Real.sqrt_le_sqrt hg)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)

theorem repeated_local_mean_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (e : ℕ) (f g : ι → ℂ) (rest : Fin e → ι → ℂ)
    (hf : (∑ x, ‖f x‖^2) ≤ Fintype.card ι)
    (hg : (∑ x, ‖g x‖^2) ≤ Fintype.card ι)
    (hrest : ∀ j, (∑ x, ‖rest j x‖^2) ≤ Fintype.card ι) :
    ‖(∑ x, f x*g x*∏ j, rest j x)/(Fintype.card ι : ℂ)‖ ≤
      (Real.sqrt (Fintype.card ι))^e := by
  classical
  have hcard : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hpoint (x : ι) : (∏ j, ‖rest j x‖) ≤ (Real.sqrt (Fintype.card ι))^e := by
    calc
      _ ≤ ∏ _ : Fin e, Real.sqrt (Fintype.card ι) := by
        apply Finset.prod_le_prod₀
        · intro j hj; exact norm_nonneg _
        · intro j hj; exact pointwise_norm_le_sqrt_card (rest j) (hrest j) x
      _ = _ := by simp
  have hsum : ‖∑ x, f x*g x*∏ j, rest j x‖ ≤
      (Fintype.card ι : ℝ)*(Real.sqrt (Fintype.card ι))^e := by
    calc
      _ ≤ ∑ x, ‖f x*g x*∏ j, rest j x‖ := norm_sum_le _ _
      _ = ∑ x, (‖f x‖*‖g x‖)*(∏ j, ‖rest j x‖) := by simp only [norm_mul, norm_prod]
      _ ≤ ∑ x, (‖f x‖*‖g x‖)*(Real.sqrt (Fintype.card ι))^e := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hpoint x) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (∑ x, ‖f x‖*‖g x‖)*(Real.sqrt (Fintype.card ι))^e :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (two_local_abs_sum_le f g hf hg)
        (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ hcard).mpr (by simpa only [mul_comm] using hsum)

end Ostmann.Construction

end

end OAI
