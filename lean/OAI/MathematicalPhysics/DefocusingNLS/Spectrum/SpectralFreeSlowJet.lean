import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalJet
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularField

namespace OAI

/-! The outgoing H solution in every angular mode of the free spectral equation. -/

namespace DefocusingNLS

noncomputable def spectralFreeSlowJet (q : ℂ) (M : ℕ) (t : ℝ) : ℂ × ℂ :=
  (normalizedSlowSolution q M (radialFreeSlowArgument t),
   2*radialFreeSlowArgument t*normalizedSlowFirst q M (radialFreeSlowArgument t))

theorem spectralFreeSlowJet_hasDerivAt (q : ℂ) (M : ℕ) (hq : -1 < q.re) (t : ℝ) :
    HasDerivAt (spectralFreeSlowJet q M)
      ((spectralFreeSlowJet q M t).2,
       -(2*(M : ℂ)-2-4*q+Complex.I*(Real.exp (2*t)/2 : ℝ))*
          (spectralFreeSlowJet q M t).2-
        4*q*(q+1-M)*(spectralFreeSlowJet q M t).1) t := by
  have hx := hasDerivAt_radialFreeSlowArgument t
  have hF := (hasDerivAt_normalizedSlowFirst_value q M (radialFreeSlowArgument t) hq
    (radialFreeSlowArgument_mem_slit t)).scomp t hx
  have hFd : HasDerivAt (fun s => normalizedSlowFirst q M (radialFreeSlowArgument s))
      (deriv (normalizedSlowFirst q M) (radialFreeSlowArgument t)*
        (2*radialFreeSlowArgument t)) t := by
    convert (hasDerivAt_normalizedSlowFirst q M (radialFreeSlowArgument t) hq
      (radialFreeSlowArgument_mem_slit t)).scomp t hx using 1
    · rfl
    · rw [(hasDerivAt_normalizedSlowFirst q M (radialFreeSlowArgument t) hq
        (radialFreeSlowArgument_mem_slit t)).deriv]
      simp only [smul_eq_mul]
      ring
  have hv : HasDerivAt (fun s => normalizedSlowSolution q M (radialFreeSlowArgument s))
      (spectralFreeSlowJet q M t).2 t := by
    exact hF
  have hd := (hx.const_mul 2).mul hFd
  have hK := normalizedSlowSolution_equation q M (radialFreeSlowArgument t) hq
    (by rw [radialFreeSlowArgument_re]) (radialFreeSlowArgument_ne_zero t)
  have hX : Complex.I*(Real.exp (2*t)/2 : ℝ) = -2*radialFreeSlowArgument t := by
    simp only [radialFreeSlowArgument]
    push_cast
    ring
  apply (hv.prodMk hd).congr_deriv
  apply Prod.ext
  · rfl
  · rw [hX]
    dsimp only [spectralFreeSlowJet]
    linear_combination 4*hK

theorem spectralFreeAngularJet_hasDerivAt (ell : ℕ) (q : ℂ)
    (hq : -1 < q.re) (t : ℝ) :
    HasDerivAt (spectralFreeSlowJet q (ell+6))
      ((spectralFreeSlowJet q (ell+6) t).2,
       -(2*((ell : ℂ)-2*q)+10)*(spectralFreeSlowJet q (ell+6) t).2-
        (((ell : ℂ)-2*q)*((ell : ℂ)-2*q+10)-((ell*(ell+10) : ℕ) : ℂ))*
          (spectralFreeSlowJet q (ell+6) t).1-
        Complex.I*(Real.exp (2*t)/2 : ℝ)*(spectralFreeSlowJet q (ell+6) t).2) t := by
  apply (spectralFreeSlowJet_hasDerivAt q (ell+6) hq t).congr_deriv
  apply Prod.ext
  · rfl
  · push_cast
    ring

theorem spectralFreeAngularPhysical_hasDerivAt (ell : ℕ) (q : ℂ)
    (hq : -1 < q.re) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (spectralPhysicalJet ((ell : ℂ)-2*q) (spectralFreeSlowJet q (ell+6)))
      ((spectralPhysicalJet ((ell : ℂ)-2*q) (spectralFreeSlowJet q (ell+6)) r).2,
       -(11/(r : ℂ)+Complex.I*(r : ℂ)/2)*
          (spectralPhysicalJet ((ell : ℂ)-2*q) (spectralFreeSlowJet q (ell+6)) r).2-
        (-Complex.I*((ell : ℂ)-2*q)/2-((ell*(ell+10) : ℕ) : ℂ)/(r : ℂ)^2)*
          (spectralPhysicalJet ((ell : ℂ)-2*q) (spectralFreeSlowJet q (ell+6)) r).1) r := by
  simpa only [one_mul,mul_one,add_zero,mul_zero,zero_div,neg_mul] using
    spectralPhysicalJet_hasDerivAt 1 ((ell : ℂ)-2*q) ((ell*(ell+10) : ℕ) : ℂ)
      (spectralFreeSlowJet q (ell+6)) r hr 0
      (by simpa only [one_mul,add_zero] using spectralFreeAngularJet_hasDerivAt ell q hq (Real.log r))

end DefocusingNLS

end OAI
