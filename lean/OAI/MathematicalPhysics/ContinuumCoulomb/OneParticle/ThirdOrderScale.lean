import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ThirdOrderBottom

namespace OAI

/-! Polynomial scales for the simultaneous third-order estimate. -/

namespace ContinuumCoulomb.Perturbation

theorem thirdOrder_scale_small {K R : ℝ} (hK : 1 ≤ K) (hR : 4*K ≤ R) :
    2*(K*R^2)+4*(2*K) ≤ R^3 := by
  have hR4 : 4 ≤ R := by linarith
  have hr2 : 4 ≤ R^2 := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hR (sq_nonneg R)
  have hsecond := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ R by linarith)
  nlinarith

theorem thirdOrder_scale_error {K R : ℝ} (hK : 1 ≤ K) (hR : 4*K ≤ R) :
    (2*(K*R^2)^2/R^3+2*(2*K))*(K/R)^2 ≤ 4*K^4/R := by
  have hRp : 0 < R := by linarith
  have hKp : 0 < K := by linarith
  apply (le_div_iff₀ hRp).mpr
  have he : ((2*(K*R^2)^2/R^3+2*(2*K))*(K/R)^2)*R =
      2*K^4+4*K^3/R := by field_simp; ring
  rw [he]
  have hKR : 2 ≤ K*R := by nlinarith
  have hk3 : 0 ≤ K^3 := by positivity
  have h : 4*K^3/R ≤ 2*K^4 := by
    apply (div_le_iff₀ hRp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hKR (show 0 ≤ 2*K^3 by positivity)]
  linarith

theorem thirdOrder_polynomial_schedule {K N : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) :
    let R := 8*K^4*N
    4*K ≤ R ∧
      2*(K*R^2)+4*(2*K) ≤ R^3 ∧
      (2*(K*R^2)^2/R^3+2*(2*K))*(K/R)^2 ≤ 1/N := by
  let R := 8*K^4*N
  have hk4 : K ≤ K^4 := le_self_pow₀ hK (by norm_num : (4:ℕ) ≠ 0)
  have hk4p : 0 < K^4 := by positivity
  have hR : 4*K ≤ R := by
    dsimp [R]
    have h := mul_le_mul_of_nonneg_left hN (show 0 ≤ 8*K^4 by positivity)
    nlinarith
  refine ⟨hR,thirdOrder_scale_small hK hR,(thirdOrder_scale_error hK hR).trans ?_⟩
  have hNp : 0 < N := by linarith
  change 4*K^4/(8*K^4*N) ≤ 1/N
  calc
    _ = 1/(2*N) := by field_simp; ring
    _ ≤ 1/N := one_div_le_one_div_of_le hNp (by linarith)

end ContinuumCoulomb.Perturbation

end OAI
