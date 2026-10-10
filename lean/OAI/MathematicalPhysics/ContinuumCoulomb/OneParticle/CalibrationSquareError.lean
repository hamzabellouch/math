import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalSquareRoot

namespace OAI

/-! Scalar error propagation for the square root appearing in the
calibrated hopping target. Negative numerical gaps are clipped at zero. -/

noncomputable section
namespace ContinuumCoulomb

theorem clipped_difference_error {u v u' v' ε : ℝ} (hgap : 0 ≤ u - v)
    (hu : |u' - u| ≤ ε) (hv : |v' - v| ≤ ε) :
    |max 0 (u' - v') - (u - v)| ≤ 2 * ε := by
  have hm := abs_max_sub_max_le_abs (u' - v') (u - v) (0 : ℝ)
  rw [max_eq_left hgap] at hm
  rw [max_comm 0 (u' - v')]
  apply hm.trans
  have he : (u' - v') - (u - v) = (u' - u) - (v' - v) := by ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hu hv).trans_eq (by ring))

theorem clipped_sqrt_difference_error {u v u' v' K ε : ℝ}
    (hK : 0 ≤ K) (hgap : 0 ≤ u - v)
    (hu : |u' - u| ≤ ε) (hv : |v' - v| ≤ ε) :
    |Real.sqrt (K * max 0 (u' - v')) - Real.sqrt (K * (u - v))| ≤
      Real.sqrt (2 * K * ε) := by
  have hs := RationalSquareRoot.sqrt_perturbation
    (mul_nonneg hK (le_max_left 0 (u' - v'))) (mul_nonneg hK hgap)
  have he : |K * max 0 (u' - v') - K * (u - v)| ≤ 2 * K * ε := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hK]
    exact (mul_le_mul_of_nonneg_left (clipped_difference_error hgap hu hv) hK).trans_eq (by ring)
  exact hs.trans (Real.sqrt_le_sqrt he)

theorem calibrated_residual_error {scale τ K T T' u v u' v' r' εT εC εR : ℝ}
    (hscale : 0 ≤ scale) (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hgap : 0 ≤ u - v)
    (hT : |T' - T| ≤ εT) (hu : |u' - u| ≤ εC) (hv : |v' - v| ≤ εC)
    (hr : |r' - Real.sqrt (K * max 0 (u' - v'))| ≤ εR) :
    |(scale * T' - τ * r') - (scale * T - τ * Real.sqrt (K * (u - v)))| ≤
      scale * εT + τ * (εR + Real.sqrt (2 * K * εC)) := by
  have hs := clipped_sqrt_difference_error hK hgap hu hv
  have ht := (abs_sub_le r' (Real.sqrt (K * max 0 (u' - v')))
    (Real.sqrt (K * (u - v)))).trans (add_le_add hr hs)
  have he : (scale * T' - τ * r') - (scale * T - τ * Real.sqrt (K * (u - v))) =
      scale * (T' - T) - τ * (r' - Real.sqrt (K * (u - v))) := by ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hscale, abs_of_nonneg hτ]
  exact add_le_add (mul_le_mul_of_nonneg_left hT hscale) (mul_le_mul_of_nonneg_left ht hτ)

end ContinuumCoulomb

end

end OAI
