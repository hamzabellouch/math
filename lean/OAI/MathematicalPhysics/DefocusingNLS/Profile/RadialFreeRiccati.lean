import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeRadialEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeInitialField
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularFluxDerivative

namespace OAI

/-! The logarithmic derivative of the actual free exterior and its real Riccati system. -/

namespace DefocusingNLS

noncomputable def radialFreeRaw (b r : ℝ) : ℂ :=
  regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (freeRadialArgument r)

noncomputable def radialFreeLog (b r : ℝ) : ℂ :=
  deriv (radialFreeRaw b) r / radialFreeRaw b r

theorem radialFreeRaw_hasDerivAt (b r : ℝ) (hr : 0 < r) :
    HasDerivAt (radialFreeRaw b)
      (freeRadialTangent r * deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6)
        (freeRadialArgument r)) r := by
  exact (analyticOnNhd_regularizedSlowSolution_slit (-Complex.I*(b : ℂ)) 6
    (by simp) _ (freeRadialArgument_mem_slit hr)).differentiableAt.hasDerivAt.scomp r
      (hasDerivAt_freeRadialArgument r)

theorem radialFreeRaw_hasDerivAt_deriv (b r : ℝ) (hr : 0 < r) :
    HasDerivAt (deriv (radialFreeRaw b))
      (-radialFreeCoefficient r*deriv (radialFreeRaw b) r-(b : ℂ)*radialFreeRaw b r) r := by
  have h := analytic_path_hasDerivAt_deriv
    (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6)
    freeRadialArgument freeRadialTangent r
    (analyticOnNhd_regularizedSlowSolution_slit (-Complex.I*(b : ℂ)) 6
      (by simp) _ (freeRadialArgument_mem_slit hr))
    hasDerivAt_freeRadialArgument (-Complex.I/2) (hasDerivAt_freeRadialTangent r)
  have he := freeRadial_raw_equation b r hr
  change deriv (deriv (radialFreeRaw b)) r +
    ((11 : ℂ)/(r : ℂ)+Complex.I*(r : ℂ)/2)*deriv (radialFreeRaw b) r+
    (b : ℂ)*radialFreeRaw b r=0 at he
  have hc : (11 : ℂ)/(r : ℂ)+Complex.I*(r : ℂ)/2=radialFreeCoefficient r := by
    simp only [radialFreeCoefficient]
    push_cast
    ring
  rw [hc] at he
  have hd := h.deriv
  change HasDerivAt (deriv (radialFreeRaw b)) _ r at h
  change deriv (deriv (radialFreeRaw b)) r = _ at hd
  rw [← hd] at h
  convert h using 1
  linear_combination -he

theorem radial_free_log_riccati (b r : ℝ) (hr : 0 < r)
    (hF : radialFreeRaw b r ≠ 0) :
    HasDerivAt (radialFreeLog b)
      (-(radialFreeLog b r)^2-radialFreeCoefficient r*radialFreeLog b r-(b : ℂ)) r := by
  have h := (radialFreeRaw_hasDerivAt_deriv b r hr).div
    (radialFreeRaw_hasDerivAt b r hr) hF
  rw [← (radialFreeRaw_hasDerivAt b r hr).deriv] at h
  apply h.congr_deriv
  dsimp [radialFreeLog]
  field_simp [hF]
  ring

theorem radialFreeLog_eq_j (b r : ℝ) (hr : 0 < r) :
    radialFreeLog b r = Complex.I*((r/2 : ℝ) : ℂ)*
      ProfileCertificate.freeProfileJ b (r^2/4) := by
  rw [ProfileCertificate.freeProfileJ_eq_log_derivative b (r^2/4)
    (div_pos (sq_pos_of_pos hr) (by norm_num))]
  dsimp [radialFreeLog]
  rw [(radialFreeRaw_hasDerivAt b r hr).deriv]
  dsimp [radialFreeRaw,freeRadialTangent,freeRadialArgument]
  ring

theorem radial_riccati_components (P : ℝ → ℂ) (b r : ℝ) (hr : r ≠ 0)
    (hP : HasDerivAt P (-(P r)^2-radialFreeCoefficient r*P r-(b : ℂ)) r) :
    HasDerivAt (fun t => (P t).re)
      (-(P r).re^2-11/r*(P r).re+((P r).im+r/4)^2-r^2/16-b) r ∧
    HasDerivAt (fun t => (P t).im+t/4)
      (-(2*(P r).re+11/r)*((P r).im+r/4)+3) r := by
  constructor
  · apply (Complex.reCLM.hasFDerivAt.comp_hasDerivAt r hP).congr_deriv
    dsimp only [Complex.reCLM_apply,radialFreeCoefficient]
    simp only [Complex.sub_re,Complex.neg_re,pow_two,Complex.mul_re,
      Complex.add_re,Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_add,
      add_zero,sub_zero]
    ring
  · apply ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hP).add
      ((hasDerivAt_id r).div_const 4)).congr_deriv
    dsimp only [Complex.imCLM_apply,radialFreeCoefficient]
    simp only [Complex.sub_im,Complex.neg_im,pow_two,Complex.mul_re,
      Complex.add_re,Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_add,
      add_zero,sub_zero]
    field_simp [hr]
    ring

end DefocusingNLS

end OAI
