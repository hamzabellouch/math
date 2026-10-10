import OAI.NumberTheory.CubicMoment.Estimates.SmallBPoissonScale

namespace OAI
noncomputable section
namespace CubicFirstMoment

lemma low_dyadic_poisson_scale {A Z : ℝ} (hA : 0 < A) (hZ : 0 < Z) :
    (A/(Z/2))*Z^2*(A/(27*(Z/2)^2))^(-(1/3:ℝ)) =
      (3*(2:ℝ)^(1/3:ℝ))*A^(2/3:ℝ)*Z^(5/3:ℝ) := by
  calc
    _ = Z^2*((A/(Z/2))*(A/(27*(Z/2)^2))^(-(1/3:ℝ))) := by ring
    _ = Z^2*(3*A^(2/3:ℝ)*(Z/2)^(-(1/3:ℝ))) := by
      rw [arbitrary_poisson_scale hA (by positivity : 0 < Z/2)]
    _ = Z^2*(3*A^(2/3:ℝ)*
        (Z^(-(1/3:ℝ))*(2:ℝ)^(1/3:ℝ))) := by
      rw [Real.div_rpow hZ.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul]
    _ = (3*(2:ℝ)^(1/3:ℝ))*A^(2/3:ℝ)*
        (Z^2*Z^(-(1/3:ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_two Z,← Real.rpow_add hZ]; norm_num

end CubicFirstMoment

end

end OAI
