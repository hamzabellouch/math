import Mathlib

namespace OAI

section

section
noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem weighted_square_shift_bound {I : Type} [Fintype I]
    (w Q a : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (ha : ∀ i, a i ∈ Set.Icc 0 δ)
    (hQ : ∀ i, Q i ≤ 1+δ) :
    (∑ i, w i*(Q i)^2)-(∑ i, w i*(Q i-a i)^2) ≤ 2*δ*(1+δ) := by
  calc
    _ = ∑ i, w i*((Q i)^2-(Q i-a i)^2) := by
      simp only [mul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ i, w i*(2*δ*(1+δ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have H1 := mul_le_mul_of_nonneg_right (hQ i) (ha i).1
      have H2 := mul_le_mul_of_nonneg_left (ha i).2 (by linarith : 0 ≤ 1+δ)
      nlinarith [sq_nonneg (a i)]
    _ = _ := by rw [← Finset.sum_mul,hs,one_mul]

theorem adaptive_endpoint_lower_algebra {I : Type} [Fintype I]
    (i₀ : I) (w Q a : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    {δ c ε f₀ f₁ p : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (ha : ∀ i, a i ∈ Set.Icc 0 δ) (hQ : ∀ i, Q i ≤ 1+δ)
    (hpath : f₁-f₀ ≤ c*(-1+2*(Q i₀-a i₀)-∑ i, w i*(Q i-a i)^2+ε))
    (hfield : f₀ ≤ p+2*c*δ) :
    f₁+c*(1-2*Q i₀+∑ i, w i*(Q i)^2)-c*(ε+2*δ*(1+δ)+2*δ) ≤ p := by
  have H := mul_le_mul_of_nonneg_left (weighted_square_shift_bound w Q a hw hs hδ ha hQ) hc
  have H0 := mul_nonneg hc (ha i₀).1
  nlinarith
end SK.Analytic

end
end

end

end OAI
