import OAI.NumberTheory.CubicMoment.Estimates.OuterSieveNumerical

namespace OAI

/-! Restoring norm scales in the outer sieve minimization. -/
noncomputable section
namespace CubicFirstMoment

lemma cube_root_cubed {x : ℝ} (hx : 0 ≤ x) : (x^(1/3:ℝ))^3 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

lemma cube_root_squared {x : ℝ} (hx : 0 ≤ x) : (x^(1/3:ℝ))^2 = x^(2/3:ℝ) := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

lemma outer_sieve_power_min {P Q J N : ℝ} (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hJ : P*Q^2 ≤ J) (hN : 0 ≤ N) :
    (J/(P*Q^2))^(1/3:ℝ)*
      min (Q*(P+N+(P*N)^(2/3:ℝ))) (P*(Q+N+(Q*N)^(2/3:ℝ))) ≤
        J+(J*N)^(2/3:ℝ)+J^(1/3:ℝ)*N := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hD : 0 < P*Q^2 := mul_pos (zero_lt_one.trans_le hP) (sq_pos_of_pos (zero_lt_one.trans_le hQ))
  have hJ0 : 0 < J := hD.trans_le hJ
  let p := P^(1/3:ℝ)
  let q := Q^(1/3:ℝ)
  let j := J^(1/3:ℝ)
  have hp : 1 ≤ p := Real.one_le_rpow hP (by norm_num)
  have hq : 1 ≤ q := Real.one_le_rpow hQ (by norm_num)
  have hp3 : p^3 = P := cube_root_cubed hP0
  have hq3 : q^3 = Q := cube_root_cubed hQ0
  have hj3 : j^3 = J := cube_root_cubed hJ0.le
  have hp2 : p^2 = P^(2/3:ℝ) := cube_root_squared hP0
  have hq2 : q^2 = Q^(2/3:ℝ) := cube_root_squared hQ0
  have hj2 : j^2 = J^(2/3:ℝ) := cube_root_squared hJ0.le
  have hroot : (P*Q^2)^(1/3:ℝ) = p*q^2 := by
    rw [Real.mul_rpow hP0 (sq_nonneg Q),← Real.rpow_pow_comm hQ0]
  have hj : p*q^2 ≤ j := by
    rw [← hroot]
    exact Real.rpow_le_rpow hD.le hJ (by norm_num)
  have hpoly := outer_sieve_polynomial_min hp hq hj hN
    (Real.rpow_nonneg hN (2/3:ℝ))
  have hmin : min (Q*(P+N+(P*N)^(2/3:ℝ))) (P*(Q+N+(Q*N)^(2/3:ℝ))) =
      min (q^3*(p^3+N+p^2*N^(2/3:ℝ)))
        (p^3*(q^3+N+q^2*N^(2/3:ℝ))) := by
    rw [hp3,hq3,hp2,hq2,Real.mul_rpow hP0 hN,Real.mul_rpow hQ0 hN]
  rw [hmin,Real.div_rpow hJ0.le hD.le,hroot]
  have hpq : p*q^2 ≠ 0 := ne_of_gt (mul_pos (zero_lt_one.trans_le hp)
    (sq_pos_of_pos (zero_lt_one.trans_le hq)))
  have hjn : (J*N)^(2/3:ℝ) = j^2*N^(2/3:ℝ) := by
    rw [Real.mul_rpow hJ0.le hN,hj2]
  calc
    _ ≤ j/(p*q^2)*((p*q^2)*(j^2+N+j*N^(2/3:ℝ))) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = J+(J*N)^(2/3:ℝ)+j*N := by
      rw [hjn]
      field_simp
      nlinarith [hj3]

end CubicFirstMoment

end

end OAI
