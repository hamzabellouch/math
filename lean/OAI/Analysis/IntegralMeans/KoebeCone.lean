import OAI.Analysis.IntegralMeans.KoebeReduction

namespace OAI

noncomputable section

namespace Brennan.Sharp

lemma right_cone_mem_disk {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) : 1 - w ∈ disk := by
  have hsq : ‖1 - w‖ ^ 2 = 1 - 2 * w.re + ‖w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hsmall' : ‖w‖ ^ 2 < ‖w‖ := by nlinarith
  have hnorm : ‖1 - w‖ < 1 := by
    nlinarith [norm_nonneg (1 - w)]
  simpa only [disk, Metric.mem_ball, dist_zero_right] using hnorm

lemma left_cone_mem_disk {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) : -1 + w ∈ disk := by
  have hr := right_cone_mem_disk h0 hsmall hcone
  have hid : (-1 : ℂ) + w = -(1 - w) := by ring
  simpa only [disk, Metric.mem_ball, dist_zero_right, hid, norm_neg] using hr

lemma norm_rpow_neg_two (w : ℂ) :
    ‖w‖ ^ (-2 : ℝ) = 1 / ‖w‖ ^ 2 := by
  simpa only [Real.rpow_two, one_div] using
    Real.rpow_neg (norm_nonneg w) (2 : ℝ)

lemma koebe_left_cone_lower {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) :
    1 / ‖w‖ ^ 2 ≤ ‖deriv koebeMap (-1 + w)‖ ^ (-2 : ℝ) := by
  rw [← norm_rpow_neg_two]
  exact koebe_negative_endpoint_lower (left_cone_mem_disk h0 hsmall hcone) hsmall

lemma koebe_right_cone_lower {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) :
    1 / ‖w‖ ^ 2 ≤ ‖deriv koebeMap (1 - w)‖ ^ (2 / 3 : ℝ) := by
  rw [← norm_rpow_neg_two]
  exact koebe_positive_endpoint_lower (right_cone_mem_disk h0 hsmall hcone) h0 hsmall

end Brennan.Sharp

end

end OAI
