import OAI.NumberTheory.CubicMoment.Estimates.CubeUniformError
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeOverlapEnergy

namespace OAI

/-! The difference between the full model square and its coprime
pair sum is supported on shared-prime pairs. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubeModelTerm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℂ) (A : ℝ) : ℂ :=
  (A^(2/3:ℝ)/9:ℝ)*cubeProfileIntegral V*((‖dispersionModel S β u‖^2:ℝ):ℂ)

theorem cube_model_coprimality_error (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 < L) (hS : ∀ a ∈ S, L ≤ norm a) :
    ‖cubeModelTerm S β u V A-coprimeCubeMainTerm S β u V A‖ ≤
      (A^(2/3:ℝ)*L^(-(1/3:ℝ))/9*‖cubeProfileIntegral V‖)*
        (∑ a ∈ S, ∑ b ∈ S, if ¬IsCoprime a b then ‖β a‖*‖β b‖ else 0) := by
  let K := A^(2/3:ℝ)*L^(-(1/3:ℝ))/9*‖cubeProfileIntegral V‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  unfold cubeModelTerm
  rw [← cube_model_quadratic S β u (cubeProfileIntegral V) A]
  unfold coprimeCubeMainTerm
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le S _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le S _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,ite_eq_right (not_not_intro hab),sub_self,norm_zero,mul_zero,le_refl]
  · simp only [ite_eq_right hab,ite_eq_left hab,sub_zero]
    have hN0 : 0 ≤ (norm (b*a))^(-(1/6:ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    rw [norm_mul,norm_mul,norm_mul,norm_star,norm_mul,norm_mul,norm_normTwist,
      norm_normTwist,mul_one,mul_one,Complex.norm_real,
      Real.norm_of_nonneg (show 0 ≤ A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9 by positivity)]
    have hn := (cube_pair_norm_bounds hL (hS a ha) (hS b hb)).2
    calc
      _ ≤ ‖β a‖*‖β b‖*(A^(2/3:ℝ)*L^(-(1/3:ℝ))/9)*‖cubeProfileIntegral V‖ := by
        gcongr
      _ = _ := by ring

end CubicFirstMoment

end

end OAI
