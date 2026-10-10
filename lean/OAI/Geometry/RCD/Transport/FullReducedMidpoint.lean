import OAI.Geometry.RCD.Transport.MidpointReducedComparison

namespace OAI

/-! # Full CD controls the exact reduced coefficient at a midpoint

The result covers zero distance and curvature, and the infinite coefficient
at a conjugate point. It is the only full-to-reduced distortion comparison
required by the midpoint construction.
-/

open Set
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem reduced_midpoint_le_tau {K N θ : ℝ} (hN : 1 < N) (hθ : 0 ≤ θ) :
    sigma K (N+1) (1/2) θ ≤ tau K N (1/2) θ := by
  by_cases hθ0 : θ=0
  · subst θ
    have hs : sigma K N (1/2) 0 = ENNReal.ofReal (1/(2*(1:ℝ))) := by simp [sigma]
    rw [tau_midpoint_of_sigma (by norm_num : (0:ℝ)<1) hs]
    simp [sigma]
  have hθp : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
  by_cases hK0 : K=0
  · subst K
    have hs : sigma 0 N (1/2) θ = ENNReal.ofReal (1/(2*(1:ℝ))) := by simp [sigma]
    rw [tau_midpoint_of_sigma (by norm_num : (0:ℝ)<1) hs]
    simp [sigma]
  rcases lt_or_gt_of_ne hK0 with hKn | hKp
  · exact reduced_midpoint_le_tau_negative hKn hN hθp
  by_cases hcut : (N-1)*Real.pi^2 ≤ K*θ^2
  · have hs : sigma K N (1/2) θ = ∞ := by
      simp only [sigma,hθ0,hK0,or_self,ite_false,ite_eq_left hcut]
    have hq : 0 < 1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0 < N)).mpr hN)
    have hh : ENNReal.ofReal (1/2:ℝ)^(1/N) ≠ 0 :=
      (ENNReal.rpow_pos (by norm_num) ENNReal.ofReal_ne_top).ne'
    have htau : tau K N (1/2) θ = ∞ := by
      unfold tau
      norm_num only [show (1/2:ℝ)≠0 by norm_num,show (1/2:ℝ)≠1 by norm_num,ite_false]
      rw [hs,ENNReal.top_rpow_of_pos hq,ENNReal.mul_top hh]
    rw [htau]
    exact le_top
  have hNm : 0 < N-1 := sub_pos.mpr hN
  have he : (θ*Real.sqrt (K/(N-1)))^2 = K*θ^2/(N-1) := by
    rw [mul_pow,Real.sq_sqrt (div_nonneg hKp.le hNm.le)]
    ring
  have hsq : (θ*Real.sqrt (K/(N-1)))^2 < Real.pi^2 := by
    rw [he,div_lt_iff₀ hNm]
    nlinarith [lt_of_not_ge hcut]
  exact reduced_midpoint_le_tau_positive hKp hN hθp (by nlinarith [Real.pi_pos])

end RegularPointCoordinates

end

end OAI
