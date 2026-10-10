import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularRayFlux

namespace OAI

/-! Vanishing of the actual outgoing flux at infinity. -/

open Filter Topology
namespace DefocusingNLS

theorem highRayPoint_affine (Z h t : ℝ) :
    highRayPoint Z h t = highRayPoint Z h 0+(t : ℂ)*highRayTangent h := by
  apply Complex.ext <;>
    norm_num [highRayPoint,highRayTangent,highRayU,highRayV,Complex.mul_re,
      Complex.mul_im] <;> ring

theorem highRayCorrection_tendsto :
    Tendsto highRayCorrection atTop (𝓝 (11/6)) := by
  have htop : Tendsto (fun t : ℝ => 1+(3/2)*t) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ)<3/2) tendsto_id)
  have hi := tendsto_inv_atTop_zero.comp htop
  have he : Tendsto (fun t : ℝ => (11/6)-(10/3)*(1+(3/2)*t)⁻¹) atTop (𝓝 (11/6)) := by
    simpa only [mul_zero,sub_zero,Function.comp_def] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (11/6 : ℝ)) atTop (𝓝 (11/6))).sub
        (hi.const_mul (10/3))
  apply he.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  dsimp [highRayCorrection]
  field_simp [show 1+(3/2)*t ≠ 0 by positivity]
  ring

theorem highRayActualFlux_tendsto_zero (q : ℂ) (M : ℕ) (Z h : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) :
    Tendsto (highRayActualFlux q M Z h) atTop (𝓝 0) := by
  let U := highRayWave q M Z h
  let g := highRayTangent h
  have hU : Tendsto U atTop (𝓝 0) := by
    change Tendsto (fun t => gaugedSlowSolution q M (highRayPoint Z h t)) atTop (𝓝 0)
    simpa only [pow_zero,one_mul] using highRay_gaugedSlowSolution_decay q M 0 hq Z h hh hZ hZ'
  have htU : Tendsto (fun t : ℝ => (t : ℂ)*U t) atTop (𝓝 0) := by
    change Tendsto (fun t : ℝ => (t : ℂ)*gaugedSlowSolution q M (highRayPoint Z h t)) atTop (𝓝 0)
    simpa only [pow_one] using highRay_gaugedSlowSolution_decay q M 1 hq Z h hh hZ hZ'
  have hD : Tendsto (deriv U) atTop (𝓝 0) := by
    have hl := (highRay_gaugedSlowSolution_derivative_decay q M 0 hq Z h hh hZ hZ').const_mul g
    simp only [pow_zero,one_mul,mul_zero] at hl
    apply hl.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (highRayWave_deriv q M Z h t hq ht).symm
  have hg0 : g ≠ 0 := by
    have hn := highRayTangent_normSq h hh
    change Complex.normSq g=1 at hn
    intro hz
    rw [hz,Complex.normSq_zero] at hn
    norm_num at hn
  have hAU : Tendsto (fun t : ℝ => (highRayPoint Z h t/g^2)*star (U t)) atTop (𝓝 0) := by
    have hl := ((hU.star).const_mul (highRayPoint Z h 0/g^2)).add
      ((htU.star).const_mul (1/g))
    simp only [star_zero,mul_zero,add_zero] at hl
    apply hl.congr'
    filter_upwards with t
    conv_rhs => rw [highRayPoint_affine]
    change highRayPoint Z h 0/g^2*star (U t)+1/g*star ((t : ℂ)*U t) =
      ((highRayPoint Z h 0+(t : ℂ)*g)/g^2)*star (U t)
    simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
    field_simp [hg0]
  have hp := hAU.mul hD
  simp only [mul_zero] at hp
  have hraw := Complex.continuous_re.tendsto 0 |>.comp hp
  have hsquare := Complex.continuous_normSq.tendsto 0 |>.comp hU
  have hcor := highRayCorrection_tendsto.mul hsquare
  change Tendsto (fun t => (highRayPoint Z h t/g^2*star (U t)*deriv U t).re+
    highRayCorrection t*Complex.normSq (U t)) atTop (𝓝 0)
  simpa only [Function.comp_def,mul_zero,Complex.zero_re,Complex.normSq_zero,add_zero]
    using hraw.add hcor

end DefocusingNLS

end OAI
