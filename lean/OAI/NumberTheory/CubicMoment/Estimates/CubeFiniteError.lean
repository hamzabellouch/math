import OAI.NumberTheory.CubicMoment.Estimates.CubePairError
import OAI.NumberTheory.CubicMoment.Estimates.CubeModel

namespace OAI

/-! Sum the literal principal-frequency error over the coprime Gram pairs. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimeCubeMainTerm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*cubeProfileIntegral W else 0

theorem cubePoissonContribution_error (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (A : ℝ), 0 < A → (∀ a ∈ S, ∀ b ∈ S, A ≤ 27*norm (b*a)) →
      ∀ (β : Eisenstein → ℂ) (u : ℝ),
      ‖cubePoissonContribution S β u W A-coprimeCubeMainTerm S β u W A‖ ≤
        ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then ‖β a‖*‖β b‖*
          (C*A/(27*Real.sqrt (norm (b*a))) +
          K*(A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9)*
            ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p) else 0 := by
  obtain ⟨C,K,hC,hK,hbound⟩ := cube_poisson_pair_error W hW hW'
  refine ⟨C,K,hC,hK,?_⟩
  intro S hS A hA hAN β u
  unfold cubePoissonContribution coprimeCubeMainTerm
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le S _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le S _).trans
  apply Finset.sum_le_sum
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    have he : (β a*normTwist u a)*star (β b*normTwist u b)*
        (A/(9*Real.sqrt (norm (b*a))):ℝ)*
          (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then gramDualTerm b a W A h else 0) -
        (β a*normTwist u a)*star (β b*normTwist u b)*
          (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*cubeProfileIntegral W =
      ((β a*normTwist u a)*star (β b*normTwist u b))*
        ((A/(9*Real.sqrt (norm (b*a))):ℝ)*
          (∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = h) then gramDualTerm b a W A h else 0) -
          (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*cubeProfileIntegral W) := by ring
    rw [he,norm_mul]
    simp only [norm_mul,norm_star,norm_normTwist,mul_one]
    exact mul_le_mul_of_nonneg_left (hbound a b (hS a ha).1 (hS a ha).2
      (hS b hb).1 (hS b hb).2 A hA (hAN a ha b hb)) (by positivity)
  · simp only [ite_eq_right hab,sub_self,norm_zero,le_refl]

end CubicFirstMoment

end

end OAI
