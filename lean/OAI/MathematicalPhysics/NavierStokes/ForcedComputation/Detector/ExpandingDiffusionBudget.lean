import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDetectorScales

namespace OAI

/-! The expanding schedule starts at time two. The initial waiting loss
and all later gate losses still fit the same fixed mass margin. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector

theorem initial_two_time_loss_lt {ν D K : ℝ}
    (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) :
    2 * ν * 3000 / initialRadius ν D K ^ 2 < 1 / 48 := by
  have he := expansion_ge_four hD
  have hk : 2 ≤ K * D + 2 := by nlinarith
  have hR : 1024 * 3000 * (1 + ν) ≤ initialRadius ν D K := by
    unfold initialRadius
    nlinarith [mul_nonneg (show 0 ≤ 1024 * 3000 * (1 + ν) by positivity)
      (show 0 ≤ expansion D * (K * D + 2) - 1 by nlinarith)]
  have hr := initialRadius_pos hν hD hK
  apply (div_lt_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith [sq_nonneg (ν - 1), sq_nonneg (initialRadius ν D K - 1024 * 3000 * (1 + ν))]

theorem total_two_time_diffusion_loss_lt {ν D K : ℝ}
    (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) :
    2 * ν * 3000 / initialRadius ν D K ^ 2 +
      (∑' n, ν * 3000 * (duration ν D K n / radius ν D K n ^ 2)) < 1 / 24 := by
  have hi := initial_two_time_loss_lt hν hD hK
  have hs := total_stage_loss_le hν hD hK
  have hr : ν / (1 + ν) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  linarith

end ForcedComputation.ExpandingDetector

end

end OAI
