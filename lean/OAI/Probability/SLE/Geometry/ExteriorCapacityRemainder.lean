import OAI.Probability.SLE.Geometry.ExteriorHerglotzPositive
import OAI.Probability.SLE.Geometry.DiskKernelRemainder

namespace OAI

/-! Capacity-relative remainder for a hydrodynamically normalized
reflected slit contained in a small disk. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

theorem exterior_capacity_remainder {G : ℂ → ℂ} {R c : ℝ}
    (hR : 0<R) (hc0 : 0<c)
    (hG : ∀ z : ℂ, R≤‖z‖ → DifferentiableAt ℂ G z)
    (hc : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 (c:ℂ)))
    (hs : ∀ z : ℂ, R≤‖z‖ → z.im*(G z-z).im≤0)
    {z : ℂ} (hz : 2*R≤‖z‖) :
    ‖G z-z-(c:ℂ)/z‖≤10*c*R/‖z‖^2 := by
  have hn : 0<‖z‖ := lt_of_lt_of_le (by linarith : 0<2*R) hz
  have hz0 : z≠0 := norm_pos_iff.mp hn
  have hR0 : (R:ℂ)≠0 := ofReal_ne_zero.mpr hR.ne'
  let w : ℂ := (R:ℂ)/z
  have hw0 : w≠0 := div_ne_zero hR0 hz0
  have hwn : ‖w‖=R/‖z‖ := by
    simp only [w,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  have hw : ‖w‖≤1/2 := by rw [hwn]; apply (div_le_iff₀ hn).mpr; linarith
  have hH := exteriorHerglotzTransform_differentiableOn hR hG hc
  have hpos := exteriorHerglotzTransform_nonneg hR hG hc hs
  have hb := positive_real_disk_kernel_remainder (div_pos hc0 hR)
    (hH.mono ball_subset_closedBall) (by simp only [exteriorHerglotzTransform_zero,ofReal_div])
    (fun v hv => hpos v (ball_subset_closedBall hv)) hw
  have hw2 : (1:ℂ)-w^2≠0 := by
    have hlt : ‖w^2‖<1 := by rw [norm_pow]; nlinarith [norm_nonneg w]
    intro he
    have he' : w^2=1 := (sub_eq_zero.mp he).symm
    rw [he',norm_one] at hlt
    exact lt_irrefl _ hlt
  have hinv : (R:ℂ)/w=z := by dsimp only [w]; field_simp
  have he : w*exteriorHerglotzTransform G R c w/(1-w^2)-(c/R:ℝ)*w=
      G z-z-(c:ℂ)/z := by
    have hm : (c/R:ℝ)*w=(c:ℂ)/z := by
      dsimp only [w]
      rw [ofReal_div]
      field_simp [hR0]
    rw [hm,exteriorHerglotzTransform_eq_raw hw0]
    unfold exteriorHerglotzRaw
    rw [hinv]
    congr 1
    field_simp [hw0,hw2]
  rw [he,hwn] at hb
  have hbR : 10*(c/R)*(R/‖z‖)^2=10*c*R/‖z‖^2 := by
    field_simp [hR.ne',hn.ne']
  rwa [hbR] at hb

end SLEExactGauge

end

end OAI
