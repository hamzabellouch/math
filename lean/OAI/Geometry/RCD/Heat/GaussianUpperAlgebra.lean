import OAI.Geometry.RCD.Heat.HeatGaussianRadius

namespace OAI

/-! # Completing the square in the Gaussian upper estimate -/

noncomputable section
namespace RegularPointCoordinates

theorem inv_sqrt_product_le_of_volume {V a b A : ℝ}
    (hV : 0 < V) (ha : 0 < a) (hb : 0 < b) (hA : 0 ≤ A)
    (hVa : V ≤ A*a) (hVb : V ≤ A*b) :
    1/(Real.sqrt a*Real.sqrt b) ≤ A/V := by
  have hs : (Real.sqrt a*Real.sqrt b)^2 = a*b := by
    rw [mul_pow,Real.sq_sqrt ha.le,Real.sq_sqrt hb.le]
  have hmul : V^2 ≤ (A*(Real.sqrt a*Real.sqrt b))^2 := by
    have hh := mul_le_mul hVa hVb hV.le (mul_nonneg hA ha.le)
    rw [mul_pow,hs]
    nlinarith only [hh]
  have h := (sq_le_sq₀ hV.le (by positivity : 0 ≤ A*(Real.sqrt a*Real.sqrt b))).mp hmul
  apply (div_le_div_iff₀ (mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb)) hV).mpr
  simpa only [one_mul] using h

theorem linear_quadratic_absorb (b z : ℝ) {η : ℝ} (hη : 0 < η) :
    b*z ≤ η*z^2+b^2/(4*η) := by
  apply (mul_le_mul_iff_right₀ (show 0 < 4*η by positivity)).mp
  have he : (4*η)*(b^2/(4*η)) = b^2 := mul_div_cancel₀ _ (by positivity)
  nlinarith only [sq_nonneg (2*η*z-b),he]

theorem gaussian_upper_absorb (N u z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    -z^2/4+(N+1+4*N*u)*z+5*N*u ≤
      -z^2/(4+ε)+(2*(N+1)^2*((4+ε)/ε)+25*N^2/4)+
        (32*N^2*((4+ε)/ε)+1)*u^2 := by
  have h4 : 0 < 4+ε := by positivity
  have hη : 0 < ε/(4*(4+ε)) := by positivity
  have hy := linear_quadratic_absorb (N+1+4*N*u) z hη
  have hB : (N+1+4*N*u)^2 ≤ 2*(N+1)^2+32*N^2*u^2 := by
    nlinarith only [sq_nonneg (N+1-4*N*u)]
  have hA : 0 ≤ (4+ε)/ε := by positivity
  have hy' : (N+1+4*N*u)*z ≤ ε/(4*(4+ε))*z^2+
      ((4+ε)/ε)*(2*(N+1)^2+32*N^2*u^2) := by
    have he : (N+1+4*N*u)^2/(4*(ε/(4*(4+ε)))) =
        ((4+ε)/ε)*(N+1+4*N*u)^2 := by field_simp
    rw [he] at hy
    exact hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left hB hA) _)
  have hz : -z^2/4+ε/(4*(4+ε))*z^2 = -z^2/(4+ε) := by
    field_simp
    ring
  have hu : 5*N*u ≤ 25*N^2/4+u^2 := by nlinarith only [sq_nonneg (5*N/2-u)]
  calc
    _ ≤ -z^2/4+(ε/(4*(4+ε))*z^2+
        ((4+ε)/ε)*(2*(N+1)^2+32*N^2*u^2))+(25*N^2/4+u^2) := by linarith only [hy',hu]
    _ = _ := by linear_combination hz

end RegularPointCoordinates

end

end OAI
