import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSmoothRampBounds

namespace OAI

/-! Explicit twice differentiable barriers for the scalar inner problem. -/

open Set
namespace DefocusingNLS

noncomputable def radialLowerBarrier (δ c m r : ℝ) : ℝ :=
  m-radialSmoothRamp δ (r-c)/50

noncomputable def radialInverseBarrier (δ c R a r : ℝ) : ℝ :=
  a+radialSmoothRamp δ (R-c)-radialSmoothRamp δ (r-c)

theorem hasDerivAt_radialRamp_shift (δ c r : ℝ) (hδ : 0 < δ) :
    HasDerivAt (fun t => radialSmoothRamp δ (t-c)) (radialSmoothRampD δ (r-c)) r := by
  convert! (hasDerivAt_radialSmoothRamp δ hδ (r-c)).comp r ((hasDerivAt_id r).sub_const c) using 1
  simp only [mul_one]

theorem hasDerivAt_radialRampD_shift (δ c r : ℝ) (hδ : 0 < δ) :
    HasDerivAt (fun t => radialSmoothRampD δ (t-c)) (radialSmoothRampDD δ (r-c)) r := by
  convert! (hasDerivAt_radialSmoothRampD δ hδ (r-c)).comp r ((hasDerivAt_id r).sub_const c) using 1
  simp only [mul_one]

theorem hasDerivAt_radialLowerBarrier (δ c m r : ℝ) (hδ : 0 < δ) :
    HasDerivAt (radialLowerBarrier δ c m) (-radialSmoothRampD δ (r-c)/50) r := by
  convert! ((hasDerivAt_radialRamp_shift δ c r hδ).div_const 50).const_sub m using 1
  ring

theorem radialLowerBarrier_laplacian (δ c m r : ℝ) (hδ : 0 < δ) :
    -deriv (deriv (radialLowerBarrier δ c m)) r-11/r*deriv (radialLowerBarrier δ c m) r=
      (radialSmoothRampDD δ (r-c)+11/r*radialSmoothRampD δ (r-c))/50 := by
  have hd : deriv (radialLowerBarrier δ c m)=fun t => -radialSmoothRampD δ (t-c)/50 :=
    funext (fun t => (hasDerivAt_radialLowerBarrier δ c m t hδ).deriv)
  have hdd := ((hasDerivAt_radialRampD_shift δ c r hδ).neg.div_const 50).deriv
  change deriv (fun t => -radialSmoothRampD δ (t-c)/50) r= -radialSmoothRampDD δ (r-c)/50 at hdd
  rw [hd,hdd]
  dsimp only
  ring

theorem hasDerivAt_radialInverseBarrier (δ c R a r : ℝ) (hδ : 0 < δ) :
    HasDerivAt (radialInverseBarrier δ c R a) (-radialSmoothRampD δ (r-c)) r := by
  exact (hasDerivAt_radialRamp_shift δ c r hδ).const_sub _

theorem radialInverseBarrier_laplacian (δ c R a r : ℝ) (hδ : 0 < δ) :
    -deriv (deriv (radialInverseBarrier δ c R a)) r-11/r*deriv (radialInverseBarrier δ c R a) r=
      radialSmoothRampDD δ (r-c)+11/r*radialSmoothRampD δ (r-c) := by
  have hd : deriv (radialInverseBarrier δ c R a)=fun t => -radialSmoothRampD δ (t-c) :=
    funext (fun t => (hasDerivAt_radialInverseBarrier δ c R a t hδ).deriv)
  have hdd := (hasDerivAt_radialRampD_shift δ c r hδ).neg.deriv
  change deriv (fun t => -radialSmoothRampD δ (t-c)) r= -radialSmoothRampDD δ (r-c) at hdd
  rw [hd,hdd]
  dsimp only
  ring

theorem radialInverseBarrier_boundary (δ c R a : ℝ) : radialInverseBarrier δ c R a R=a := by
  unfold radialInverseBarrier
  ring

theorem radialInverseBarrier_bounds (δ c R a : ℝ) (hδ : 0 < δ) (hcR : c ≤ R)
    (r : ℝ) (hr : r ∈ Icc 0 R) :
    a ≤ radialInverseBarrier δ c R a r ∧
      radialInverseBarrier δ c R a r ≤ a+(R-c)^2 := by
  have hmono := monotone_radialSmoothRamp δ hδ (sub_le_sub_right hr.2 c)
  have hramp := radialSmoothRamp_bounds δ hδ (r-c)
  have hR := (radialSmoothRamp_bounds δ hδ (R-c)).2.1
  rw [max_eq_left (sub_nonneg.2 hcR)] at hR
  unfold radialInverseBarrier
  constructor <;> linarith [hramp.1]

end DefocusingNLS

end OAI
