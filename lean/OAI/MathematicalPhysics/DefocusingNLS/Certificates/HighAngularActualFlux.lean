import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularFluxDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularCorrections
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularPathEquation

namespace OAI

/-! The positive multiplier identity for the actual gauged outgoing solution. -/

namespace DefocusingNLS

noncomputable def highArcWave (q : ℂ) (M : ℕ) (Z h : ℝ) (t : ℝ) : ℂ :=
  gaugedSlowSolution q M (highArcPoint Z h t)

noncomputable def highArcActualFlux (q : ℂ) (M : ℕ) (Z h : ℝ) : ℝ → ℝ :=
  highAngularFlux (fun t => highArcPoint Z h t/(highArcTangent h t)^2)
    (highArcCorrection Z) (highArcWave q M Z h)

theorem highAngular_radialPotential_re (u v h M : ℝ) (hh : h=1 ∨ h= -1) (hv : v ≠ 0) :
    (((u : ℂ)-Complex.I*(h*v : ℝ))/4+
      (M : ℂ)^2/(4*((u : ℂ)-Complex.I*(h*v : ℝ)))).re =
      u/4+M^2*u/(4*(u^2+v^2)) := by
  have hd : u^2+v^2 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg u) (sq_pos_of_ne_zero hv))
  rcases hh with rfl | rfl <;>
    simp only [Complex.add_re,Complex.div_re,Complex.mul_re,Complex.mul_im,
      Complex.sub_re,Complex.sub_im,pow_two,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,Complex.normSq_apply] <;> norm_num <;> field_simp <;> ring

theorem highArcWave_deriv (q : ℂ) (M : ℕ) (Z h t : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1) (hZ : 2704/1000 ≤ Z)
    (ht : 0 ≤ 2*t) (ht' : 2*t ≤ highArcAngle) :
    deriv (highArcWave q M Z h) t =
      highArcTangent h t*deriv (gaugedSlowSolution q M) (highArcPoint Z h t) := by
  have hx : 0 ≤ (highArcPoint Z h t).re := by
    rw [highArcPoint_re]
    exact (highArc_geometry Z (2*t) hZ ht ht').1
  have hd := (hasDerivAt_gaugedSlowSolution q M (highArcPoint Z h t) hq hx
    (highArcPoint_ne_zero Z h t hh hZ ht ht')).differentiableAt.hasDerivAt
  change deriv (fun s : ℝ => gaugedSlowSolution q M (highArcPoint Z h s)) t =
    highArcTangent h t*deriv (gaugedSlowSolution q M) (highArcPoint Z h t)
  simpa only [Function.comp_def,smul_eq_mul] using
    (hd.scomp t (hasDerivAt_highArcPoint Z h t)).deriv

theorem hasDerivAt_highArcActualFlux (q : ℂ) (M : ℕ) (Z h t : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1) (hZ : 2704/1000 ≤ Z)
    (ht : 0 ≤ 2*t) (ht' : 2*t ≤ highArcAngle) :
    HasDerivAt (highArcActualFlux q M Z h)
      (highArcL Z (2*t)*Complex.normSq
          (deriv (highArcWave q M Z h) t+
            ((3/10 : ℂ)-Complex.I*(h : ℂ))*highArcWave q M Z h t)+
        highArcPotential (3-(((M : ℂ)+1)/2-q).re) (M : ℝ) Z (2*t)*
          Complex.normSq (highArcWave q M Z h t)) t := by
  let γ := highArcPoint Z h
  let g := highArcTangent h
  let U := highArcWave q M Z h
  let A := fun s => γ s/(g s)^2
  let C : ℂ := Complex.I*(h*2 : ℝ)
  let E : ℂ := ((M : ℂ)+1)/2-q
  let V : ℂ := γ t/4+(M : ℂ)^2/(4*γ t)
  have hgeo := highArc_geometry Z (2*t) hZ ht ht'
  have hx : 0 ≤ (γ t).re := by rw [highArcPoint_re]; exact hgeo.1
  have hx0 : γ t ≠ 0 := highArcPoint_ne_zero Z h t hh hZ ht ht'
  have hs : γ t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    rcases hx.eq_or_lt with he | he
    · exact Or.inr (fun hi => hx0 (Complex.ext he.symm hi))
    · exact Or.inl he
  have hg0 : g t ≠ 0 := by
    intro hz
    have hn := highArcTangent_normSq h t hh
    change Complex.normSq (g t)=1 at hn
    rw [hz,Complex.normSq_zero] at hn
    norm_num at hn
  have hg : HasDerivAt g (-C*g t) t := by
    convert! hasDerivAt_highArcTangent h t hh using 1
    dsimp [C]
    ring
  have hF := analyticOnNhd_gaugedSlowSolution q M hq (γ t) hs
  have hU : HasDerivAt U (deriv U t) t := by
    have h := hF.differentiableAt.hasDerivAt.scomp t (hasDerivAt_highArcPoint Z h t)
    exact h.differentiableAt.hasDerivAt
  have hU' : HasDerivAt (deriv U) (deriv (deriv U) t) t :=
    (analytic_path_hasDerivAt_deriv (gaugedSlowSolution q M) γ g t hF
      (hasDerivAt_highArcPoint Z h) (-C*g t) hg).differentiableAt.hasDerivAt
  have hA := hasDerivAt_kineticCoefficient γ g t C
    (hasDerivAt_highArcPoint Z h t) hg hg0
  have hODE := gaugedSlowSolution_path_equation q M γ g t C hq hx hx0 hg0
    (hasDerivAt_highArcPoint Z h) hg
  have hODE' : -A t*deriv (deriv U) t-
      (1/g t+2*C*A t-C*A t)*deriv U t+V*U t=E*U t := by
    change -A t*deriv (deriv U) t-(1/g t+C*A t)*deriv U t+V*U t=E*U t at hODE
    linear_combination hODE
  have hB := hasDerivAt_highArcCorrection Z t
  have hd := hasDerivAt_highAngularFlux_completed A (highArcCorrection Z) U t
    (highArcL Z (2*t)) (highArcN Z (2*t)) (3/10)
    ((3/10)*(Real.cos (2*t)-4*highArcN Z (2*t))) 2
    (Real.sin (2*t)+4*highArcL Z (2*t)) h
    (1/g t+2*C*A t) V E (deriv U t) (deriv (deriv U) t) hh
    (highArc_kinetic_coefficient Z h t hh) (by dsimp [highArcCorrection]; ring)
    hA (by convert! hB using 1; ring) hU hU' (by
      convert! hODE' using 1)
  have hV : V.re = highArcU (2*t)/4+
      (M : ℝ)^2*highArcU (2*t)/(4*(highArcU (2*t)^2+highArcV Z (2*t)^2)) := by
    convert! highAngular_radialPotential_re (highArcU (2*t)) (highArcV Z (2*t)) h M hh hgeo.2.1.ne' using 1
    simp only [V,γ,highArcPoint,Complex.ofReal_mul,Complex.ofReal_natCast]
    ring_nf
  convert! hd using 1
  rw [hV]
  dsimp only [highArcPotential,E,U,highArcWave]
  push_cast
  ring_nf

end DefocusingNLS

end OAI
