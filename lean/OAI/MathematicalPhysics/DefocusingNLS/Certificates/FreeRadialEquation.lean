import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeRadialProfile

namespace OAI

/-! The free exterior profile satisfies the radial stationary equation. -/

namespace DefocusingNLS

noncomputable def freeRadialArgument (r : ℝ) : ℂ := -Complex.I*((r^2/4 : ℝ) : ℂ)
noncomputable def freeRadialTangent (r : ℝ) : ℂ := -Complex.I*((r/2 : ℝ) : ℂ)

theorem hasDerivAt_freeRadialArgument (r : ℝ) :
    HasDerivAt freeRadialArgument (freeRadialTangent r) r := by
  convert! (((hasDerivAt_id r).pow 2).div_const 4).ofReal_comp.const_mul (-Complex.I) using 1
  try simp only [freeRadialTangent,id_eq]
  push_cast
  ring

theorem hasDerivAt_freeRadialTangent (r : ℝ) :
    HasDerivAt freeRadialTangent (-Complex.I/2) r := by
  convert! ((hasDerivAt_id r).div_const 2).ofReal_comp.const_mul (-Complex.I) using 1
  try simp only [freeRadialTangent,id_eq]
  push_cast
  ring

theorem freeRadialArgument_mem_slit {r : ℝ} (hr : 0 < r) :
    freeRadialArgument r ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.2
  right
  simp only [freeRadialArgument,neg_mul,Complex.neg_im,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,one_mul,zero_add]
  nlinarith [sq_pos_of_pos hr]

theorem freeRadial_raw_equation (b r : ℝ) (hr : 0 < r) :
    let F := fun t => regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (freeRadialArgument t)
    deriv (deriv F) r + ((11 : ℂ)/(r : ℂ)+Complex.I*(r : ℂ)/2)*deriv F r+
      (b : ℂ)*F r=0 := by
  intro F
  have hq : -1 < (-Complex.I*(b : ℂ)).re := by simp
  have hA := analyticOnNhd_regularizedSlowSolution_slit (-Complex.I*(b : ℂ)) 6 hq
    _ (freeRadialArgument_mem_slit hr)
  obtain ⟨h₁,h₂⟩ := analytic_path_derivatives
    (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6)
    freeRadialArgument freeRadialTangent r hA hasDerivAt_freeRadialArgument
    (-Complex.I/2) (hasDerivAt_freeRadialTangent r)
  have hx : 0 ≤ (freeRadialArgument r).re := by
    simp only [freeRadialArgument,neg_mul,Complex.neg_re,Complex.mul_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,mul_zero,sub_self,neg_zero,le_refl]
  have hx0 : freeRadialArgument r ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 hr.ne') (by norm_num)))
  have hK := regularizedSlowSolution_kummer_equation_closed
    (-Complex.I*(b : ℂ)) 6 (freeRadialArgument r) hq hx hx0
  change deriv (deriv (fun t => regularizedSlowSolution (-Complex.I*(b : ℂ)) 6
      (freeRadialArgument t))) r+_+_=0
  rw [h₁,h₂]
  let H := regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (freeRadialArgument r)
  let D := deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (freeRadialArgument r)
  let DD := deriv (deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6)) (freeRadialArgument r)
  change (-Complex.I/2)*D+(freeRadialTangent r)^2*DD+
    ((11 : ℂ)/(r : ℂ)+Complex.I*(r : ℂ)/2)*(freeRadialTangent r*D)+(b : ℂ)*H=0
  change freeRadialArgument r*DD+((6 : ℂ)-freeRadialArgument r)*D-
    (-Complex.I*(b : ℂ))*H=0 at hK
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  calc
    _ = -Complex.I*(freeRadialArgument r*DD+((6 : ℂ)-freeRadialArgument r)*D-
        (-Complex.I*(b : ℂ))*H) := by
      dsimp only [freeRadialArgument,freeRadialTangent]
      push_cast
      field_simp [hr0]
      ring_nf
      simp only [Complex.I_sq]
      ring
    _ = 0 := by rw [hK,mul_zero]

end DefocusingNLS

end OAI
