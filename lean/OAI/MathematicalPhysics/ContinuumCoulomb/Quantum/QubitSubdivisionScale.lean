import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionMatrix

namespace OAI

/-! Polynomial scales for simultaneous subdivision. -/

namespace ContinuumCoulomb

theorem qmaSubdivision_scale_small {K R : ℝ} (hK : 1 ≤ K) (hR : 4*K ≤ R) :
    2*(K*R)+4*(2*K) ≤ R^2 := by
  have hRp : 0 ≤ R := by linarith
  have h4 : 4 ≤ R := by linarith
  have ha := mul_le_mul_of_nonneg_right hR hRp
  have hb : 4*R ≤ R^2 := by nlinarith
  nlinarith

theorem qmaSubdivision_scale_error {K R : ℝ} (hK : 1 ≤ K) (hR : 4*K ≤ R) :
    (2*(K*R)^2/R^2+2*(2*K))*(K/R)^2 ≤ 6*K^4/R^2 := by
  have hRp : 0 < R := by linarith
  have hK34 : K^3 ≤ K^4 := pow_le_pow_right₀ hK (by norm_num)
  apply (le_div_iff₀ (sq_pos_of_pos hRp)).mpr
  have he : ((2*(K*R)^2/R^2+2*(2*K))*(K/R)^2)*R^2 = 2*K^4+4*K^3 := by
    field_simp
    ring
  rw [he]
  nlinarith

theorem qmaSubdivision_total_error {K R : ℝ} (hK : 1 ≤ K) (hR : 4*K ≤ R) :
    (2*(K*R)^2/R^2+2*(2*K))*(K/R)^2+K^2/R^2 ≤ 7*K^4/R := by
  have hRp : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hK24 : K^2 ≤ K^4 := pow_le_pow_right₀ hK (by norm_num)
  calc
    _ ≤ 6*K^4/R^2+K^4/R^2 := add_le_add (qmaSubdivision_scale_error hK hR)
      (div_le_div_of_nonneg_right hK24 (sq_nonneg R))
    _ = 7*K^4/R^2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hRp (by nlinarith)

end ContinuumCoulomb

end OAI
