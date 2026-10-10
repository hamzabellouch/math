import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVolterraCalculus

namespace OAI

/-! A canonical family of actual radial solutions for the shooting argument. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def radialShootingAmplitude (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖)
    (a r : ℝ) : ℝ :=
  a+radialVolterra (radialInitialForcing R (1+L*R) N
    (radialShootingState R L M hR hL hM N hN hBound hLip a)) r

theorem differentiable_radialShootingAmplitude (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖) (a : ℝ) :
    Differentiable ℝ (radialShootingAmplitude R L M hR hL hM N hN hBound hLip a) := by
  intro r
  have hf := continuous_radialInitialForcing R (1+L*R) N hN
    (radialShootingState R L M hR hL hM N hN hBound hLip a)
  exact ((hasDerivAt_radialVolterra _ hf r).const_add a).differentiableAt

theorem differentiableAt_deriv_radialShootingAmplitude (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖)
    (a r : ℝ) (hr : r ≠ 0) :
    DifferentiableAt ℝ (deriv (radialShootingAmplitude R L M hR hL hM N hN hBound hLip a)) r := by
  let f := radialInitialForcing R (1+L*R) N
    (radialShootingState R L M hR hL hM N hN hBound hLip a)
  have hf : Continuous f := continuous_radialInitialForcing R (1+L*R) N hN _
  have he : deriv (radialShootingAmplitude R L M hR hL hM N hN hBound hLip a)=
      fun t => t*radialAverage f t := by
    funext t
    exact ((hasDerivAt_radialVolterra f hf t).const_add a).deriv
  rw [he]
  exact ((hasDerivAt_id r).mul (hasDerivAt_radialAverage f hf r hr)).differentiableAt

theorem radialShootingAmplitude_eq (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖)
    (a r : ℝ) (hr : r ∈ Icc 0 R) :
    radialShootingAmplitude R L M hR hL hM N hN hBound hLip a r=
      Real.exp ((1+L*R)*r)*radialShootingState R L M hR hL hM N hN hBound hLip a r := by
  rw [radialShootingState_fixed R L M hR hL hM N hN hBound hLip a r]
  simp only [radialInitialPicard,radialClamp_eq R r hr,radialShootingAmplitude]
  rw [← mul_assoc,← Real.exp_add]
  ring_nf
  simp only [Real.exp_zero,mul_one]

theorem radialShootingAmplitude_equation (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖)
    (a : ℝ) :
    let A := radialShootingAmplitude R L M hR hL hM N hN hBound hLip a
    Continuous A ∧ A 0=a ∧ HasDerivAt A 0 0 ∧
      (∀ r ∈ Icc 0 R, A r=a+radialVolterra (fun t => N t (A t)) r) ∧
      (∀ r ∈ Ioo 0 R, deriv (deriv A) r+11/r*deriv A r=N r (A r)) := by
  let A := radialShootingAmplitude R L M hR hL hM N hN hBound hLip a
  let v := radialShootingState R L M hR hL hM N hN hBound hLip a
  let f := radialInitialForcing R (1+L*R) N v
  have hf : Continuous f := continuous_radialInitialForcing R (1+L*R) N hN v
  have hd (r : ℝ) : HasDerivAt A (r*radialAverage f r) r := by
    convert! (hasDerivAt_radialVolterra f hf r).const_add a using 1
  have heq : EqOn f (fun t => N t (A t)) (Icc 0 R) := by
    intro r hr
    dsimp only [f,radialInitialForcing]
    rw [radialClamp_eq R r hr]
    rw [show A r=Real.exp ((1+L*R)*r)*v r from
      radialShootingAmplitude_eq R L M hR hL hM N hN hBound hLip a r hr]
  refine ⟨(show Differentiable ℝ A from fun r => (hd r).differentiableAt).continuous,?_,?_,?_,?_⟩
  · simp only [radialShootingAmplitude,radialVolterra_zero,add_zero]
  · simpa only [zero_mul] using hd 0
  · intro r hr
    change a+radialVolterra f r=a+radialVolterra (fun t => N t (A t)) r
    rw [radialVolterra_congr f _ r hr.1 (fun t ht => heq ⟨ht.1,ht.2.trans hr.2⟩)]
  · intro r hr
    have hderiv : deriv A=deriv (radialVolterra f) := by
      funext t
      exact (hd t).deriv.trans (hasDerivAt_radialVolterra f hf t).deriv.symm
    rw [hderiv,radialVolterra_radial_equation f hf r hr.1.ne']
    exact heq ⟨hr.1.le,hr.2.le⟩

theorem continuous_radialShootingAmplitude_endpoint (R L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖) :
    Continuous (fun a => radialShootingAmplitude R L M hR hL hM N hN hBound hLip a R) := by
  have he : (fun a => radialShootingAmplitude R L M hR hL hM N hN hBound hLip a R)=
      fun a => Real.exp ((1+L*R)*R)*
        radialShootingState R L M hR hL hM N hN hBound hLip a R := by
    funext a
    exact radialShootingAmplitude_eq R L M hR hL hM N hN hBound hLip a R ⟨hR,le_rfl⟩
  rw [he]
  exact continuous_radialShootingEndpoint R L M hR hL hM N hN hBound hLip

end DefocusingNLS

end OAI
