import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialStationaryReconstruction

namespace OAI

/-! Second differentiability of the amplitude-phase reconstruction. -/

open Set
namespace DefocusingNLS

theorem radialPolar_deriv_differentiableAt (A φ : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hφ : Differentiable ℝ φ) (r : ℝ)
    (hDA : DifferentiableAt ℝ (deriv A) r) (hDφ : DifferentiableAt ℝ (deriv φ) r) :
    DifferentiableAt ℝ (deriv (radialPolar A φ)) r := by
  have hd : deriv (radialPolar A φ)=fun t =>
      ((((deriv A t : ℝ) : ℂ)+Complex.I*(A t : ℂ)*((deriv φ t : ℝ) : ℂ))*
        Complex.exp (Complex.I*(φ t : ℂ))) :=
    funext (fun t => (radialPolar_hasDerivAt A φ hA hφ t).deriv)
  rw [hd]
  exact ((hDA.hasDerivAt.ofReal_comp.add
    ((((hA r).hasDerivAt.ofReal_comp).const_mul Complex.I).mul hDφ.hasDerivAt.ofReal_comp)).mul
      (radialPhaseExp_hasDerivAt φ hφ r)).differentiableAt

theorem radialInnerComplex_deriv_differentiableAt (R a : ℝ) (hR : 0 ≤ R)
    (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hAP : ∀ t ∈ Icc 0 R, 0 < A t) (r : ℝ) (hr : r ∈ Ioo 0 R)
    (hDA : DifferentiableAt ℝ (deriv A) r) :
    DifferentiableAt ℝ (deriv (radialInnerComplex R a A)) r := by
  let B := radialClampedAmplitude R A
  have hB : Continuous B := radialClampedAmplitude_continuous R A hA.continuous
  have hn : ∀ t, B t ≠ 0 := fun t => (hAP _ (radialClamp_mem R t hR)).ne'
  have hφ := radialPhase_differentiable (6-2*a) B hB hn
  have hφ' := radialPhase_deriv_hasDerivAt (6-2*a) (deriv A r) B hB hn r hr.1.ne'
    (radialClampedAmplitude_hasDerivAt R A hA r hr)
  exact radialPolar_deriv_differentiableAt A _ hA hφ r hDA hφ'.differentiableAt

end DefocusingNLS

end OAI
