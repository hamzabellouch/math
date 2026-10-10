import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! The exact unitary diagonal propagator in the slow exterior tail system. -/

namespace DefocusingNLS

noncomputable def radialExteriorPhase (t s : ℝ) : ℂ :=
  Complex.exp (Complex.I*((Real.exp (2*s)-Real.exp (2*t))/4 : ℝ))

noncomputable def radialExteriorPropagator (t s : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (v.1,radialExteriorPhase t s*v.2)

theorem radialExteriorPhase_norm (t s : ℝ) : ‖radialExteriorPhase t s‖=1 := by
  change ‖Complex.exp (Complex.I*((Real.exp (2*s)-Real.exp (2*t))/4 : ℝ))‖=1
  rw [Complex.norm_exp]
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Real.exp_zero]

theorem radialExteriorPropagator_norm (t s : ℝ) (v : ℂ × ℂ) :
    ‖radialExteriorPropagator t s v‖=‖v‖ := by
  simp only [radialExteriorPropagator,Prod.norm_def,norm_mul,radialExteriorPhase_norm,one_mul]

theorem radialExteriorPropagator_self (t : ℝ) (v : ℂ × ℂ) :
    radialExteriorPropagator t t v=v := by
  simp [radialExteriorPropagator,radialExteriorPhase]

theorem radialExteriorPropagator_comp (t s u : ℝ) (v : ℂ × ℂ) :
    radialExteriorPropagator t s (radialExteriorPropagator s u v)=radialExteriorPropagator t u v := by
  apply Prod.ext
  · rfl
  · change radialExteriorPhase t s*(radialExteriorPhase s u*v.2)=radialExteriorPhase t u*v.2
    rw [← mul_assoc]
    congr 1
    unfold radialExteriorPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem radialExteriorPropagator_sub (t s : ℝ) (v w : ℂ × ℂ) :
    radialExteriorPropagator t s (v-w)=radialExteriorPropagator t s v-radialExteriorPropagator t s w := by
  apply Prod.ext
  · rfl
  · exact mul_sub _ _ _

theorem radialExteriorPropagator_hasDerivAt (t s : ℝ) (v : ℂ × ℂ) :
    HasDerivAt (fun r => radialExteriorPropagator r s v)
      ((0 : ℂ),-Complex.I*(Real.exp (2*t)/2 : ℝ)*radialExteriorPhase t s*v.2) t := by
  have he : HasDerivAt (fun r : ℝ => Real.exp (2*r)) (2*Real.exp (2*t)) t := by
    convert ((hasDerivAt_id t).const_mul 2).exp using 1 <;> simp [mul_comm]
  have hθ := ((he.const_sub (Real.exp (2*s))).div_const 4).ofReal_comp
  have hp := ((hθ.const_mul Complex.I).cexp).mul_const v.2
  have hv : HasDerivAt (fun r => radialExteriorPhase r s*v.2)
      (-Complex.I*(Real.exp (2*t)/2 : ℝ)*radialExteriorPhase t s*v.2) t := by
    apply hp.congr_deriv
    change Complex.exp (Complex.I*((Real.exp (2*s)-Real.exp (2*t))/4 : ℝ))*
      (Complex.I*((-(2*Real.exp (2*t))/4 : ℝ) : ℂ))*v.2=
      -Complex.I*(Real.exp (2*t)/2 : ℝ)*
        Complex.exp (Complex.I*((Real.exp (2*s)-Real.exp (2*t))/4 : ℝ))*v.2
    have heq : ((-(2*Real.exp (2*t))/4 : ℝ) : ℂ) = -((Real.exp (2*t)/2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq]
    ring
  exact (hasDerivAt_const t v.1).prodMk hv

end DefocusingNLS

end OAI
