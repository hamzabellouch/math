import Mathlib

namespace OAI

open scoped BigOperators
namespace Ostmann.Characters
section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_sum_sq_le_gram (f : ι → E) {B ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i, ‖f i‖^2 ≤ B)
    (hoff : ∀ i j, i≠j → ‖inner ℂ (f i) (f j)‖ ≤ ε) :
    ‖∑ i, f i‖^2 ≤ (Fintype.card ι : ℝ)*B+(Fintype.card ι : ℝ)^2*ε := by
  classical
  have he : ‖∑ i, f i‖^2 = ∑ i, ∑ j, RCLike.re (inner ℂ (f i) (f j)) := by
    rw [@norm_sq_eq_re_inner ℂ]
    simp only [sum_inner, inner_sum, map_sum]
    rw [Finset.sum_comm]
  rw [he]
  calc
    _ ≤ ∑ i : ι, ∑ j : ι, ((if j=i then B else 0)+ε) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : j=i
      · subst j
        simp only [ite_true]
        rw [← @norm_sq_eq_re_inner ℂ]
        exact (hdiag i).trans (le_add_of_nonneg_right hε)
      · simp only [hij, ite_false, zero_add]
        exact (Complex.re_le_norm _).trans (hoff i j (Ne.symm hij))
    _ = _ := by simp [Finset.sum_add_distrib, pow_two]; ring

theorem permutation_comparison (f : ι → E) (v : E) (η : ℂ)
    {B ε : ℝ} (hε : 0 ≤ ε) (hmean : ∀ i, inner ℂ v (f i) = η)
    (hdiag : ∀ i, ‖f i‖^2 ≤ B)
    (hoff : ∀ i j, i≠j → ‖inner ℂ (f i) (f j)‖ ≤ ε) :
    (Fintype.card ι : ℝ)^2 * ‖η‖^2 ≤
      ‖v‖^2 * ((Fintype.card ι : ℝ)*B+(Fintype.card ι : ℝ)^2*ε) := by
  have hc := norm_inner_le_norm (𝕜 := ℂ) v (∑ i, f i)
  have hsq : ‖inner ℂ v (∑ i, f i)‖^2 ≤ ‖v‖^2 * ‖∑ i, f i‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hc
  have he : inner ℂ v (∑ i, f i) = (Fintype.card ι : ℂ)*η := by
    simp only [inner_sum, hmean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [he, norm_mul, Complex.norm_natCast, mul_pow] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_left (norm_sum_sq_le_gram f hε hdiag hoff)
    (sq_nonneg _))
end
end Ostmann.Characters

end OAI
