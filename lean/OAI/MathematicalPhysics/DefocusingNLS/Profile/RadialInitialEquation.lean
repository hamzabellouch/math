import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInitialValueExistence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVolterraCalculus

namespace OAI

/-! The constructed fixed point solves the radial amplitude equation with its initial data. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_radialInitialEquation (R a₀ L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖) :
    ∃ A : ℝ → ℝ, Continuous A ∧ A 0=a₀ ∧ HasDerivAt A 0 0 ∧
      (∀ r ∈ Icc 0 R, A r=a₀+radialVolterra (fun t => N t (A t)) r) ∧
      (∀ r ∈ Ioo 0 R, deriv (deriv A) r+11/r*deriv A r=N r (A r)) := by
  obtain ⟨v,hv,-⟩ := existsUnique_radialInitialPicard R a₀ L M hR hL hM N hN hBound hLip
  let η := 1+L*R
  let f := radialInitialForcing R η N v
  have hf : Continuous f := continuous_radialInitialForcing R η N hN v
  let A : ℝ → ℝ := fun r => a₀+radialVolterra f r
  have hd (r : ℝ) : HasDerivAt A (r*radialAverage f r) r := by
    convert! (hasDerivAt_radialVolterra f hf r).const_add a₀ using 1
  have he (r : ℝ) (hr : r ∈ Icc 0 R) :
      A r=Real.exp (η*r)*v r := by
    rw [hv r]
    simp only [radialInitialPicard,radialClamp_eq R r hr]
    change a₀+radialVolterra f r=Real.exp (η*r)*
      (Real.exp (-η*r)*(a₀+radialVolterra f r))
    rw [← mul_assoc,← Real.exp_add]
    ring_nf
    simp only [Real.exp_zero,mul_one]
  have heq : EqOn f (fun t => N t (A t)) (Icc 0 R) := by
    intro r hr
    dsimp only [f,radialInitialForcing]
    rw [radialClamp_eq R r hr,he r hr]
  refine ⟨A,?_,?_,?_,?_,?_⟩
  · exact (show Differentiable ℝ A from fun r => (hd r).differentiableAt).continuous
  · simp only [A,radialVolterra_zero,add_zero]
  · simpa only [zero_mul] using hd 0
  · intro r hr
    change a₀+radialVolterra f r=a₀+radialVolterra (fun t => N t (A t)) r
    rw [radialVolterra_congr f _ r hr.1 (fun t ht => heq ⟨ht.1,ht.2.trans hr.2⟩)]
  · intro r hr
    have hderiv : deriv A=deriv (radialVolterra f) := by
      funext t
      exact (hd t).deriv.trans (hasDerivAt_radialVolterra f hf t).deriv.symm
    rw [hderiv,radialVolterra_radial_equation f hf r hr.1.ne']
    exact heq ⟨hr.1.le,hr.2.le⟩

end DefocusingNLS

end OAI
