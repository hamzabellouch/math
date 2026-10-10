import OAI.NumberTheory.CubicMoment.Estimates.CubeScalar
import OAI.NumberTheory.CubicMoment.Estimates.CoprimeDispersionPoisson

namespace OAI

/-! The cube main term is the squared model polynomial, with the exact
primary-coset density 1/9. This is a finite identity without asymptotics. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cube_model_pair_factor (a b : Eisenstein) :
    (norm (b*a))^(-(1/6:ℝ)) = (norm a)^(-(1/6:ℝ))*(norm b)^(-(1/6:ℝ)) := by
  rw [norm_mul_eq,Real.mul_rpow (norm_nonneg _) (norm_nonneg _),mul_comm]

theorem cube_model_quadratic (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (I : ℂ) (A : ℝ) :
    (∑ a ∈ S, ∑ b ∈ S,
      (β a*normTwist u a)*star (β b*normTwist u b)*
        (A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9:ℝ)*I) =
      (A^(2/3:ℝ)/9:ℝ)*I*((‖dispersionModel S β u‖^2:ℝ):ℂ) := by
  have hs (x : ℝ) : star (x:ℂ) = (x:ℂ) := by simp
  rw [dispersionModel,complex_sum_norm_sq_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [cube_model_pair_factor]
  simp only [star_mul,hs,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring_nf

end CubicFirstMoment

end

end OAI
