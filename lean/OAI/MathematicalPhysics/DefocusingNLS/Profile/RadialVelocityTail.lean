import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformTailDeformation

namespace OAI

/-! The velocity of each actual matched profile has linear growth at infinity. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedVelocity_div_tendsto (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    Tendsto (fun r : ℝ => radialMatchedVelocity n z r/r) atTop (nhds (1/2 : ℝ)) := by
  let ν := radialShootingNu (n+radialInnerShootingThreshold) z
  let Z := radialExteriorCanonical ν (n+radialInnerShootingThreshold) (radialShootingM z)
    (Real.log innerBoundaryRadius)
  have hZ : Tendsto Z atTop (nhds (radialShootingM z,0)) :=
    (radialExteriorCanonical_spec hX).2.1.tendsto
  have hξ : Tendsto (fun r : ℝ => (Z (Real.log r)).2/(Z (Real.log r)).1)
      atTop (nhds (0 : ℂ)) := by
    simpa only [zero_div,Function.comp_def,Pi.div_apply] using
      (hZ.snd_nhds.div hZ.fst_nhds (radialShootingM_ne_zero z)).comp Real.tendsto_log_atTop
  have hscale : Tendsto (fun r : ℝ => 2/r^2) atTop (nhds (0 : ℝ)) := by
    have hh := (tendsto_inv_atTop_zero.pow 2).const_mul (2 : ℝ)
    simpa only [zero_pow (by decide : 2≠0),mul_zero,inv_pow,div_eq_mul_inv] using hh
  have hi := (Complex.continuous_im.tendsto (0 : ℂ)).comp hξ
  have ht := (tendsto_const_nhds (x := (1/2 : ℝ))).add
    (hscale.mul ((tendsto_const_nhds (x := ν.im)).add hi))
  simp only [Complex.zero_im,add_zero,zero_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop innerBoundaryRadius] with r hr
  exact (radialMatchedVelocity_logarithmic n z hX hz r hr).symm

theorem radialMatchedVelocity_eventually_bound (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    ∀ᶠ r : ℝ in atTop, |radialMatchedVelocity n z r| ≤ r := by
  have ht := (radialMatchedVelocity_div_tendsto n z hX hz).norm.eventually
    (gt_mem_nhds (by norm_num : ‖(1/2 : ℝ)‖ < 1))
  filter_upwards [ht,eventually_gt_atTop (0 : ℝ)] with r hr hr0
  rw [norm_div,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hr0] at hr
  exact ((div_lt_one hr0).mp hr).le

end DefocusingNLS

end OAI
