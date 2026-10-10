import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSmoothBarrier

namespace OAI

/-! Regularity and exact flat/quadratic pieces of the radial barriers. -/

namespace DefocusingNLS

theorem radialSmoothRamp_flat (δ x : ℝ) (hx : x ≤ 0) :
    radialSmoothRamp δ x=0 ∧ radialSmoothRampD δ x=0 ∧ radialSmoothRampDD δ x=0 := by
  simp only [radialSmoothRamp,radialSmoothRampD,radialSmoothRampDD,radialSplice,ite_eq_left hx,and_self]

theorem radialSmoothRamp_quadratic (δ x : ℝ) (hδ : 0 < δ) (hx : δ < x) :
    radialSmoothRamp δ x=x^2-δ*x+δ^2/3 ∧
    radialSmoothRampD δ x=2*x-δ ∧ radialSmoothRampDD δ x=2 := by
  simp only [radialSmoothRamp,radialSmoothRampD,radialSmoothRampDD,
    radialRampInner,radialRampInnerD,radialRampInnerDD,radialSplice,
    ite_eq_right (not_le_of_gt (hδ.trans hx)),ite_eq_right (not_le_of_gt hx),and_self]

theorem differentiable_radialLowerBarrier (δ c m : ℝ) (hδ : 0 < δ) :
    Differentiable ℝ (radialLowerBarrier δ c m) :=
  fun r => (hasDerivAt_radialLowerBarrier δ c m r hδ).differentiableAt

theorem differentiable_deriv_radialLowerBarrier (δ c m : ℝ) (hδ : 0 < δ) :
    Differentiable ℝ (deriv (radialLowerBarrier δ c m)) := by
  have hd : deriv (radialLowerBarrier δ c m)=fun r => -radialSmoothRampD δ (r-c)/50 :=
    funext (fun r => (hasDerivAt_radialLowerBarrier δ c m r hδ).deriv)
  rw [hd]
  exact fun r => ((hasDerivAt_radialRampD_shift δ c r hδ).neg.div_const 50).differentiableAt

theorem differentiable_radialInverseBarrier (δ c R a : ℝ) (hδ : 0 < δ) :
    Differentiable ℝ (radialInverseBarrier δ c R a) :=
  fun r => (hasDerivAt_radialInverseBarrier δ c R a r hδ).differentiableAt

theorem differentiable_deriv_radialInverseBarrier (δ c R a : ℝ) (hδ : 0 < δ) :
    Differentiable ℝ (deriv (radialInverseBarrier δ c R a)) := by
  have hd : deriv (radialInverseBarrier δ c R a)=fun r => -radialSmoothRampD δ (r-c) :=
    funext (fun r => (hasDerivAt_radialInverseBarrier δ c R a r hδ).deriv)
  rw [hd]
  exact fun r => (hasDerivAt_radialRampD_shift δ c r hδ).neg.differentiableAt

end DefocusingNLS

end OAI
