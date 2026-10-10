import OAI.NumberTheory.CubicMoment.Estimates.PoissonDyadicSum

namespace OAI

/-! Exact normalization of the small-B Poisson bound on one dyadic
coefficient interval. -/
noncomputable section
namespace CubicFirstMoment

lemma arbitrary_poisson_scale {A N : ℝ} (hA : 0 < A) (hN : 0 < N) :
    (A/N)*(A/(27*N^2))^(-(1/3:ℝ)) =
      3*A^(2/3:ℝ)*N^(-(1/3:ℝ)) := by
  apply (mul_right_inj' (sq_pos_of_pos hN).ne').mp
  calc
    _ = A*N*(A/(27*N^2))^(-(1/3:ℝ)) := by field_simp
    _ = 3*A^(2/3:ℝ)*N^(5/3:ℝ) := cubic_poisson_scale hA hN
    _ = _ := by
      have he : N^(5/3:ℝ) = N^2*N^(-(1/3:ℝ)) := by
        rw [← Real.rpow_natCast N 2,← Real.rpow_add hN]
        norm_num
      rw [he]
      ring

lemma smallB_dyadic_poisson_scale {A Z : ℝ} (hA : 0 < A) (hZ : 0 < Z) :
    (A/(Z/2))*Z^(1-1/40000:ℝ)*(A/(27*(Z/2)^2))^(-(1/3:ℝ)) =
      (3*(2:ℝ)^(1/3:ℝ))*A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ) := by
  calc
    _ = Z^(1-1/40000:ℝ)*((A/(Z/2))*(A/(27*(Z/2)^2))^(-(1/3:ℝ))) := by ring
    _ = Z^(1-1/40000:ℝ)*(3*A^(2/3:ℝ)*(Z/2)^(-(1/3:ℝ))) := by
      rw [arbitrary_poisson_scale hA (by positivity : 0 < Z/2)]
    _ = Z^(1-1/40000:ℝ)*(3*A^(2/3:ℝ)*
        (Z^(-(1/3:ℝ))*(2:ℝ)^(1/3:ℝ))) := by
      rw [Real.div_rpow hZ.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul]
    _ = (3*(2:ℝ)^(1/3:ℝ))*A^(2/3:ℝ)*
        (Z^(1-1/40000:ℝ)*Z^(-(1/3:ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add hZ]; norm_num

end CubicFirstMoment

end

end OAI
