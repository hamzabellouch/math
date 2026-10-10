import OAI.Analysis.Mahler.TailIntegral

namespace OAI

namespace SymmetricMahler
open Real Set MeasureTheory

/-- The pointwise quadratic angular estimate. -/
theorem angular_speed_upper {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    angularSpeed r θ ≤ (8*r/(Real.pi^2*(1-r^2)))*θ := by
  have hden : 0 < 1-r^2 := by nlinarith
  have hs : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ hθπ
  have ha := arctan_le_argument (show 0 ≤ 2*r*sin θ/(1-r^2) by positivity)
  have hb : 2*r*sin θ/(1-r^2) ≤ 2*r*θ/(1-r^2) := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sin_le hθ) (by positivity)) hden.le
  dsimp [angularSpeed]
  calc
    _ ≤ (4/Real.pi^2)*(2*r*θ/(1-r^2)) := mul_le_mul_of_nonneg_left (ha.trans hb) (by positivity)
    _ = _ := by field_simp; ring

lemma angular_speed_integrable (r a b : ℝ) :
    IntervalIntegrable (angularSpeed r) volume a b := by
  apply Continuous.intervalIntegrable
  unfold angularSpeed
  fun_prop

/-- Integrating angular speed on an arc of length d gives a d² bound. -/
theorem angular_speed_integral_bound {r d : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hd : 0 ≤ d) (hdπ : d ≤ Real.pi) :
    (∫ θ in (0 : ℝ)..d, angularSpeed r θ) ≤ 4*r*d^2/(Real.pi^2*(1-r^2)) := by
  calc
    _ ≤ ∫ θ in (0 : ℝ)..d, (8*r/(Real.pi^2*(1-r^2)))*θ := by
      apply intervalIntegral.integral_mono_on hd (angular_speed_integrable r 0 d)
        ((continuous_const.mul continuous_id).intervalIntegrable 0 d)
      intro θ hθ
      exact angular_speed_upper hr hr1 hθ.1 (hθ.2.trans hdπ)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring

/-- The square-root sine lower bound, with the explicit constant c=1. -/
theorem sine_bound_of_increment {r d Δ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hd : 0 ≤ d) (hdπ : d ≤ Real.pi/2)
    (hΔ : Δ ≤ 4*r*d^2/(Real.pi^2*(1-r^2))) :
    sqrt ((1-r^2)*Δ/r) ≤ sin d := by
  have hden : 0 < 1-r^2 := by nlinarith
  have hp : 0 < Real.pi^2 := by positivity
  have hsq : (1-r^2)*Δ/r ≤ ((2/Real.pi)*d)^2 := by
    have hh := mul_le_mul_of_nonneg_left hΔ (show 0 ≤ (1-r^2)/r by positivity)
    calc
      _ = ((1-r^2)/r)*Δ := by ring
      _ ≤ ((1-r^2)/r)*(4*r*d^2/(Real.pi^2*(1-r^2))) := hh
      _ = _ := by field_simp; ring
  have hsqrt : sqrt ((1-r^2)*Δ/r) ≤ (2/Real.pi)*d := by
    apply sqrt_le_iff.2
    exact ⟨by positivity, hsq⟩
  exact hsqrt.trans (Real.mul_le_sin hd hdπ)

/-- The sine estimate follows directly from the angular integral identity. -/
theorem sine_bound_of_angular_integral {r d Δ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hd : 0 ≤ d) (hdπ : d ≤ Real.pi/2)
    (hΔ : Δ = ∫ θ in (0 : ℝ)..d, angularSpeed r θ) :
    sqrt ((1-r^2)*Δ/r) ≤ sin d := by
  apply sine_bound_of_increment hr hr1 hd hdπ
  rw [hΔ]
  exact angular_speed_integral_bound hr hr1 hd (by linarith [Real.pi_pos])

end SymmetricMahler

end OAI
