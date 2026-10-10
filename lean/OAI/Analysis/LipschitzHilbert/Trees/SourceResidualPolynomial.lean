import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledResidualEnvelope

namespace OAI

/-! Polynomial good-path thresholds control the actual residual square
with an exponent fixed before the path and the mass cutoff are chosen. -/

noncomputable section
namespace LipschitzHilbert

theorem residual_square_polynomial_bound {L C A E S R c q p r : ℝ}
    (hL : 6 ≤ L) (hC : 0 ≤ C) (hA : 0 ≤ A) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hCb : C ≤ L^c) (hAb : A ≤ L^q) (hEb : E ≤ L^p) (hSb : S ≤ L^p)
    (hRb : R ≤ L^r) :
    3*C^2*A^2*(E^2+R*S^2) ≤ (L^(c+q+p+r+1))^2 := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hR1 : 1 ≤ L^r := Real.one_le_rpow hL1 hr
  have hEsq := pow_le_pow_left₀ hE hEb 2
  have hSsq := pow_le_pow_left₀ hS hSb 2
  have hCq := pow_le_pow_left₀ hC hCb 2
  have hAq := pow_le_pow_left₀ hA hAb 2
  have hES : E^2+R*S^2 ≤ 2*L^r*(L^p)^2 := by
    have hmul := mul_le_mul hRb hSsq (sq_nonneg S) (Real.rpow_nonneg hL0.le r)
    have hOne := mul_le_mul_of_nonneg_right hR1 (sq_nonneg (L^p))
    nlinarith
  calc
    _ ≤ 3*(L^c)^2*(L^q)^2*(2*L^r*(L^p)^2) := by
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hCq (by norm_num)) hAq
        (sq_nonneg A) (by positivity)) hES (by positivity) (by positivity)
    _ = 6*L^(2*c+2*q+r+2*p) := by
      rw [← Real.rpow_mul_natCast hL0.le,← Real.rpow_mul_natCast hL0.le,
        ← Real.rpow_mul_natCast hL0.le]
      push_cast
      rw [Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_add hL0]
      ring_nf
    _ ≤ L*L^(2*c+2*q+r+2*p) :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L^(2*c+2*q+r+2*p+1) := by
      calc
        _ = L^(2*c+2*q+r+2*p)*L^(1:ℝ) := by rw [Real.rpow_one]; ring
        _ = _ := (Real.rpow_add hL0 _ _).symm
    _ ≤ L^(2*(c+q+p+r+1)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    _ = _ := by rw [← Real.rpow_mul_natCast hL0.le]; push_cast; congr 1; ring

end LipschitzHilbert

end

end OAI
