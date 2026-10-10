import OAI.MeasureTheory.Falconer.Angular.AngularNonstationaryPower

namespace OAI

namespace PlanarFalconer

theorem stationary_half_cancel {Λ : ℝ} (hΛ : 0 < Λ) :
    Λ^(1/2:ℝ)*Λ^(-1/2:ℝ) = 1 := by
  rw [← Real.rpow_add hΛ]
  norm_num

theorem inverse_local_remainder_factor (q j : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (A P C D : ℝ) :
    (Λ^(1/2:ℝ)*(Λ⁻¹)^j) *
      (Λ^(-1/2:ℝ)*A*P*C*D^(2*j+2)*(D^2/Λ)^(q+1)) =
        A*P*C*D^2*(D^2/Λ)^(q+1+j) := by
  calc
    _ = (Λ^(1/2:ℝ)*Λ^(-1/2:ℝ)) *
        (A*P*C*D^2*((Λ⁻¹)^j*D^(2*j))*(D^2/Λ)^(q+1)) := by
      rw [pow_add D (2*j) 2]; ring
    _ = A*P*C*D^2*(D^2/Λ)^(q+1+j) := by
      rw [stationary_half_cancel hΛ]
      simp only [div_pow, pow_add, pow_mul]
      ring

theorem inverse_nonstationary_remainder_factor (j J : ℕ) (Λ B P C D : ℝ) :
    (Λ^(1/2:ℝ)*(Λ⁻¹)^j) * (B*P*C*D^(2*j+2*J)/Λ^(2*J)) =
      B*P*C*(D^2/Λ)^j*(D^2/Λ)^J*(Λ^(1/2:ℝ)*(Λ^J)⁻¹) := by
  simp only [div_pow, pow_add, pow_mul]
  ring

theorem inverse_nonstationary_remainder_bound (j J : ℕ) (hJ : 1 ≤ J)
    {Λ B P C D : ℝ} (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hratio : D^2/Λ ≤ 1) :
    (Λ^(1/2:ℝ)*(Λ⁻¹)^j) * (B*P*C*D^(2*j+2*J)/Λ^(2*J)) ≤
      B*P*C*D^2*(D^2/Λ)^J := by
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hr0 : 0 ≤ D^2/Λ := by positivity
  have hrj : (D^2/Λ)^j ≤ 1 := pow_le_one₀ hr0 hratio
  have hh : Λ^(1/2:ℝ)*(Λ^J)⁻¹ ≤ 1 := by
    calc
      _ ≤ Λ^(1/2:ℝ)*Λ^(-1/2:ℝ) :=
        mul_le_mul_of_nonneg_left (angular_even_decay_half hΛ hJ) (by positivity)
      _ = 1 := stationary_half_cancel hΛp
  have hD2 : 1 ≤ D^2 := one_le_pow₀ hD
  rw [inverse_nonstationary_remainder_factor]
  calc
    _ ≤ B*P*C*1*(D^2/Λ)^J*1 := by gcongr
    _ ≤ B*P*C*D^2*(D^2/Λ)^J := by
      simp only [mul_one]
      exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) hD2) (by positivity)

end PlanarFalconer

end OAI
