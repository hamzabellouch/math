import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularActualFlux
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularRayDecay

namespace OAI

/-! The actual positive flux on the straight outgoing contour. -/

namespace DefocusingNLS

noncomputable def highRayWave (q : ℂ) (M : ℕ) (Z h : ℝ) (t : ℝ) : ℂ :=
  gaugedSlowSolution q M (highRayPoint Z h t)

noncomputable def highRayActualFlux (q : ℂ) (M : ℕ) (Z h : ℝ) : ℝ → ℝ :=
  highAngularFlux (fun t => highRayPoint Z h t/(highRayTangent h)^2)
    highRayCorrection (highRayWave q M Z h)

theorem highRayWave_deriv (q : ℂ) (M : ℕ) (Z h t : ℝ)
    (hq : -1 < q.re) (ht : 0 ≤ t) :
    deriv (highRayWave q M Z h) t =
      highRayTangent h*deriv (gaugedSlowSolution q M) (highRayPoint Z h t) := by
  have hx : 0 ≤ (highRayPoint Z h t).re := by
    rw [highRayPoint_re]
    dsimp [highRayU]
    positivity
  have hd := (hasDerivAt_gaugedSlowSolution q M (highRayPoint Z h t) hq hx
    (highRayPoint_ne_zero Z h t ht)).differentiableAt.hasDerivAt
  change deriv (fun s : ℝ => gaugedSlowSolution q M (highRayPoint Z h s)) t =
    highRayTangent h*deriv (gaugedSlowSolution q M) (highRayPoint Z h t)
  simpa only [Function.comp_def,smul_eq_mul] using
    (hd.scomp t (hasDerivAt_highRayPoint Z h t)).deriv

theorem hasDerivAt_highRayActualFlux (q : ℂ) (M : ℕ) (Z h t : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) (ht : 0 ≤ t) :
    HasDerivAt (highRayActualFlux q M Z h)
      (highRayL Z t*Complex.normSq
          (deriv (highRayWave q M Z h) t+
            (highRayCorrection t/highRayL Z t : ℝ)*highRayWave q M Z h t)+
        highRayPotential (3-(((M : ℂ)+1)/2-q).re) (M : ℝ) Z t*
          Complex.normSq (highRayWave q M Z h t)) t := by
  let γ := highRayPoint Z h
  let g := fun _ : ℝ => highRayTangent h
  let U := highRayWave q M Z h
  let A := fun s => γ s/(g s)^2
  let E : ℂ := ((M : ℂ)+1)/2-q
  let V : ℂ := γ t/4+(M : ℂ)^2/(4*γ t)
  obtain ⟨hu,_,hv,_,hL⟩ := highRay_bounds Z t hZ hZ' ht
  have hu0 : 0 < highRayU t := by linarith
  have hL0 : highRayL Z t ≠ 0 := by linarith
  have hx : 0 ≤ (γ t).re := by rw [highRayPoint_re]; exact hu0.le
  have hx0 : γ t ≠ 0 := highRayPoint_ne_zero Z h t ht
  have hs : γ t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    rw [highRayPoint_re]
    exact hu0
  have hg0 : g t ≠ 0 := by
    intro hz
    have hn := highRayTangent_normSq h hh
    change Complex.normSq (g t)=1 at hn
    rw [hz,Complex.normSq_zero] at hn
    norm_num at hn
  have hg : HasDerivAt g (-(0 : ℂ)*g t) t := by simpa using hasDerivAt_const t (highRayTangent h)
  have hF := analyticOnNhd_gaugedSlowSolution q M hq (γ t) hs
  have hU : HasDerivAt U (deriv U t) t :=
    (hF.differentiableAt.hasDerivAt.scomp t (hasDerivAt_highRayPoint Z h t)).differentiableAt.hasDerivAt
  have hU' : HasDerivAt (deriv U) (deriv (deriv U) t) t :=
    (analytic_path_hasDerivAt_deriv (gaugedSlowSolution q M) γ g t hF
      (hasDerivAt_highRayPoint Z h) (-(0 : ℂ)*g t) hg).differentiableAt.hasDerivAt
  have hA := hasDerivAt_kineticCoefficient γ g t 0 (hasDerivAt_highRayPoint Z h t) hg hg0
  have hODE := gaugedSlowSolution_path_equation q M γ g t 0 hq hx hx0 hg0
    (hasDerivAt_highRayPoint Z h) hg
  change -A t*deriv (deriv U) t-(1/g t+0*A t)*deriv U t+V*U t=E*U t at hODE
  have hd := hasDerivAt_highAngularFlux_completed A highRayCorrection U t
    (highRayL Z t) (highRayN Z t) (highRayCorrection t/highRayL Z t)
    (5/(1+(3/2)*t)^2) 0 0 h (1/g t) V E (deriv U t) (deriv (deriv U) t) hh
    (highRay_kinetic_coefficient Z h t hh)
    (by field_simp [hL0]; ring)
    (by simpa using hA) (by simpa using hasDerivAt_highRayCorrection t ht)
    hU hU' (by simpa only [mul_zero,zero_mul,sub_zero,add_zero,Complex.ofReal_zero] using hODE)
  have hV : V.re = highRayU t/4+
      (M : ℝ)^2*highRayU t/(4*(highRayU t^2+highRayV Z t^2)) := by
    convert! highAngular_radialPotential_re (highRayU t) (highRayV Z t) h M hh hv.ne' using 1
    simp only [V,γ,highRayPoint,Complex.ofReal_mul,Complex.ofReal_natCast]
    ring_nf
  norm_num only [mul_zero,zero_mul,zero_div,Complex.ofReal_zero,sub_zero,add_zero,pow_two] at hd
  have hc : V.re-E.re+5/(1+(3/2)*t)^2-
      highRayL Z t*(highRayCorrection t/highRayL Z t)^2 =
      highRayPotential (3-E.re) (M : ℝ) Z t := by
    rw [hV]
    dsimp only [highRayPotential]
    rw [highRayCorrection_quotient t ht]
    have hden : 1+(3/2)*t ≠ 0 := by positivity
    field_simp [hL0,hden]
    ring
  simp only [pow_two] at hc
  rw [hc] at hd
  exact hd


end DefocusingNLS

end OAI
