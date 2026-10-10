import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! Derivatives of the actual complex amplitude-phase reconstruction. -/

namespace DefocusingNLS

noncomputable def radialPolar (A φ : ℝ → ℝ) (r : ℝ) : ℂ :=
  (A r : ℂ)*Complex.exp (Complex.I*(φ r : ℂ))

theorem radialPhaseExp_hasDerivAt (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (r : ℝ) :
    HasDerivAt (fun t => Complex.exp (Complex.I*(φ t : ℂ)))
      (Complex.I*((deriv φ r : ℝ) : ℂ)*Complex.exp (Complex.I*(φ r : ℂ))) r := by
  convert! (((hφ r).hasDerivAt.ofReal_comp).const_mul Complex.I).cexp using 1
  ring

theorem radialPolar_hasDerivAt (A φ : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hφ : Differentiable ℝ φ) (r : ℝ) :
    HasDerivAt (radialPolar A φ)
      ((((deriv A r : ℝ) : ℂ)+Complex.I*(A r : ℂ)*((deriv φ r : ℝ) : ℂ))*
        Complex.exp (Complex.I*(φ r : ℂ))) r := by
  convert! ((hA r).hasDerivAt.ofReal_comp).mul (radialPhaseExp_hasDerivAt φ hφ r) using 1
  ring

theorem radialPolar_second_derivative (A φ : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hφ : Differentiable ℝ φ) (r : ℝ)
    (hDA : DifferentiableAt ℝ (deriv A) r) (hDφ : DifferentiableAt ℝ (deriv φ) r) :
    deriv (deriv (radialPolar A φ)) r=
      ((((deriv (deriv A) r : ℝ) : ℂ)-(A r : ℂ)*((deriv φ r : ℝ) : ℂ)^2)+
        Complex.I*(2*((deriv A r : ℝ) : ℂ)*((deriv φ r : ℝ) : ℂ)+
          (A r : ℂ)*((deriv (deriv φ) r : ℝ) : ℂ)))*Complex.exp (Complex.I*(φ r : ℂ)) := by
  have hd : deriv (radialPolar A φ)=fun t =>
      ((((deriv A t : ℝ) : ℂ)+Complex.I*(A t : ℂ)*((deriv φ t : ℝ) : ℂ))*
        Complex.exp (Complex.I*(φ t : ℂ))) :=
    funext (fun t => (radialPolar_hasDerivAt A φ hA hφ t).deriv)
  have hZ := hDA.hasDerivAt.ofReal_comp.add
    ((((hA r).hasDerivAt.ofReal_comp).const_mul Complex.I).mul hDφ.hasDerivAt.ofReal_comp)
  have he := (hZ.mul (radialPhaseExp_hasDerivAt φ hφ r)).deriv
  rw [hd]
  change deriv (fun t => ((((deriv A t : ℝ) : ℂ)+Complex.I*(A t : ℂ)*((deriv φ t : ℝ) : ℂ))*
    Complex.exp (Complex.I*(φ t : ℂ)))) r= _ at he
  rw [he]
  dsimp only [Pi.add_apply,Pi.mul_apply]
  linear_combination ((A r : ℂ)*((deriv φ r : ℝ) : ℂ)^2*Complex.exp (Complex.I*(φ r : ℂ)))*Complex.I_sq

theorem radialPolar_norm (A φ : ℝ → ℝ) (r : ℝ) : ‖radialPolar A φ r‖=|A r| := by
  unfold radialPolar
  rw [norm_mul,Complex.norm_exp]
  simp

end DefocusingNLS

end OAI
