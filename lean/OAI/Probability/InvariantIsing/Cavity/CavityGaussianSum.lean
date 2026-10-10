import OAI.Probability.InvariantIsing.Cavity.CavityGaussianAffineImage
import Mathlib.Probability.Independence.CharacteristicFunction

namespace OAI

/-! The finite sums of independent Gaussian increments used in the cavity path. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix

namespace InvariantIsing

theorem cavity_gaussian_sum_law {ι : Type*} [Fintype ι] {d : ℕ}
    (S : ι → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef) :
    (Measure.pi (fun i => multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i))).map
        (fun z => ∑ i, z i) = multivariateGaussian 0 (∑ i, S i) := by
  have hsum : (∑ i, S i).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun i _ => hS i)
  apply Measure.ext_of_charFun
  rw [charFun_map_sum_pi_eq_prod]
  funext x
  simp only [Finset.prod_apply, charFun_multivariateGaussian, hS, hsum, inner_zero_right,
    Complex.ofReal_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  have hquad : x ⬝ᵥ (∑ i, S i) *ᵥ x = ∑ i, x ⬝ᵥ S i *ᵥ x := by
    simp only [Matrix.sum_mulVec, dotProduct_sum]
  rw [hquad]
  simp only [Complex.ofReal_sum, Finset.sum_div, Finset.sum_neg_distrib]

theorem cavity_gaussian_add_law {d : ℕ}
    (S T : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (hT : T.PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).prod
      (multivariateGaussian 0 T)).map (fun p => p.1 + p.2) =
      multivariateGaussian 0 (S + T) := by
  apply Measure.ext_of_charFun
  rw [charFun_map_add_prod_eq_mul]
  funext x
  simp only [Pi.mul_apply, charFun_multivariateGaussian hS,
    charFun_multivariateGaussian hT, charFun_multivariateGaussian (hS.add hT),
    inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [← Complex.exp_add]
  congr 1
  rw [Matrix.add_mulVec, dotProduct_add]
  push_cast
  ring

end InvariantIsing

end

end OAI
