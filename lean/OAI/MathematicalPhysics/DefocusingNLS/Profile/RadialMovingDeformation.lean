import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMovingTail
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorVelocity

namespace OAI

/-! Both actual radial deformation eigenvalues approach one half along escaping tails. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialShootingNu_subsequence_tendsto (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (nhds z₀)) :
    Tendsto (fun i => radialShootingNu (s i) (z i)) atTop
      (nhds (-2*radialShootingQ z₀)) := by
  have hq := continuous_radialShootingQ.continuousAt.tendsto.comp hz
  simpa only [radialShootingNu,Function.comp_def,sub_zero] using!
    (hq.const_mul (-2)).sub
      ((tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1/(n : ℂ)) atTop (nhds 0)).comp hs.tendsto_atTop)

theorem radialMatched_moving_deformation (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (nhds z₀)) (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop)
    (hX : ∀ i, HasRadialExterior
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i))
      (Real.log innerBoundaryRadius))
    (hmatch : ∀ i, radialMatchingMap (s i) (z i)=0) :
    let w := fun i => radialVelocity (6-2*radialShootingA (s i))
      (fun t => ‖radialMatchedProfile (s i) (z i) t‖)
    Tendsto (fun i => w i (r i)/r i) atTop (nhds (1/2 : ℝ)) ∧
    Tendsto (fun i => deriv (w i) (r i)) atTop (nhds (1/2 : ℝ)) := by
  intro w
  let N := fun i => s i+radialInnerShootingThreshold
  have hN : StrictMono N := fun i j hij => Nat.add_lt_add_right (hs hij) _
  let ν := fun i => radialShootingNu (N i) (z i)
  let Z := fun i => radialExteriorCanonical (ν i) (N i) (radialShootingM (z i))
    (Real.log innerBoundaryRadius)
  let ξ := fun i => (Z i (Real.log (r i))).2/(Z i (Real.log (r i))).1
  have hjet := radialShooting_moving_tail N hN z z₀ hz
    (fun i => Real.log (r i)) (Real.tendsto_log_atTop.comp hr)
  have hξ : Tendsto ξ atTop (nhds (0 : ℂ)) := by
    simpa only [zero_div,Pi.div_apply,ξ,Z,ν] using!
      hjet.snd_nhds.div hjet.fst_nhds (radialShootingM_ne_zero z₀)
  have hν := radialShootingNu_subsequence_tendsto N hN z z₀ hz
  have hscale : Tendsto (fun i => 2/(r i)^2) atTop (nhds (0 : ℝ)) := by
    have hh := ((tendsto_inv_atTop_zero.comp hr).pow 2).const_mul 2
    simpa only [zero_pow (by decide : 2 ≠ 0),mul_zero,Function.comp_def,inv_pow,div_eq_mul_inv] using hh
  have hνr := (Complex.continuous_re.tendsto (-2*radialShootingQ z₀)).comp hν
  have hνi := (Complex.continuous_im.tendsto (-2*radialShootingQ z₀)).comp hν
  have hξr := (Complex.continuous_re.tendsto (0 : ℂ)).comp hξ
  have hξi := (Complex.continuous_im.tendsto (0 : ℂ)).comp hξ
  have htan : Tendsto (fun i => 1/2+2/(r i)^2*((ν i).im+(ξ i).im))
      atTop (nhds (1/2 : ℝ)) := by
    have hh := (tendsto_const_nhds (x := (1/2 : ℝ))).add (hscale.mul (hνi.add hξi))
    simpa only [Complex.zero_im,add_zero,zero_mul,add_zero,Function.comp_def,ν] using! hh
  have hrad : Tendsto (fun i => 1/2-(ξ i).re-
      2/(r i)^2*((ν i).im+(ξ i).im)*(11+2*(ν i).re+2*(ξ i).re))
      atTop (nhds (1/2 : ℝ)) := by
    have hh := ((tendsto_const_nhds (x := (1/2 : ℝ))).sub hξr).sub
      ((hscale.mul (hνi.add hξi)).mul
        (((tendsto_const_nhds (x := (11 : ℝ))).add (hνr.const_mul 2)).add (hξr.const_mul 2)))
    simpa only [Complex.zero_re,Complex.zero_im,sub_zero,zero_mul,Function.comp_def,ν] using! hh
  constructor
  · apply htan.congr'
    filter_upwards [hr.eventually (eventually_gt_atTop innerBoundaryRadius)] with i hi
    exact (radialMatchedVelocity_logarithmic (s i) (z i) (hX i) (hmatch i) (r i) hi).symm
  · apply hrad.congr'
    filter_upwards [hr.eventually (eventually_gt_atTop innerBoundaryRadius)] with i hi
    exact (radialMatchedDeformation_logarithmic (s i) (z i) (hX i) (hmatch i) (r i) hi).symm

end DefocusingNLS

end OAI
