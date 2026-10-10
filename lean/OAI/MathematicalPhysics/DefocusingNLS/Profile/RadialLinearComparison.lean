import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMinimumPrinciple
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace OAI

/-! Comparison for the small-ball operator `-Δ-V+q`, using a positive Gaussian. -/

open Set
namespace DefocusingNLS

theorem radialGaussian_hasDerivAt (r : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (t^2/24))
      ((r/12)*Real.exp (r^2/24)) r := by
  convert! (((hasDerivAt_id r).pow 2).div_const 24).exp using 1
  simp only [Pi.pow_apply,id_eq]
  ring

theorem radialGaussian_product_deriv (u : ℝ → ℝ) (hu : Differentiable ℝ u) (r : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (t^2/24)*u t)
      (Real.exp (r^2/24)*(deriv u r+r/12*u r)) r := by
  convert! (radialGaussian_hasDerivAt r).mul (hu r).hasDerivAt using 1
  ring

theorem radialGaussian_operator_identity (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (r : ℝ) (hr : r ≠ 0) (hdu : DifferentiableAt ℝ (deriv u) r) :
    let w := fun t : ℝ => Real.exp (t^2/24)*u t
    deriv (deriv w) r+(11/r-r/6)*deriv w r=
      Real.exp (r^2/24)*(deriv (deriv u) r+11/r*deriv u r+(1-r^2/144)*u r) := by
  let w := fun t : ℝ => Real.exp (t^2/24)*u t
  have hw : deriv w=fun t => Real.exp (t^2/24)*(deriv u t+t/12*u t) :=
    funext (fun t => (radialGaussian_product_deriv u hu t).deriv)
  have hD := hdu.hasDerivAt.add (((hasDerivAt_id r).div_const 12).mul (hu r).hasDerivAt)
  have hDD := ((radialGaussian_hasDerivAt r).mul hD).deriv
  change deriv (fun t => Real.exp (t^2/24)*(deriv u t+t/12*u t)) r=
    (r/12*Real.exp (r^2/24))*(deriv u r+r/12*u r)+
      Real.exp (r^2/24)*(deriv (deriv u) r+(1/12*u r+r/12*deriv u r)) at hDD
  change deriv (deriv w) r+(11/r-r/6)*deriv w r=_
  rw [hw,hDD]
  dsimp only
  field_simp [hr]
  ring

theorem radial_linear_comparison (R : ℝ) (hR : 0 < R) (hR2 : R^2 ≤ 11)
    (u V q : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hdu : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv u) r)
    (hu0 : deriv u 0=0) (huR : 0 ≤ u R)
    (hV : ∀ r ∈ Ioo 0 R, V r ≤ (1/2 : ℝ))
    (hq : ∀ r ∈ Ioo 0 R, 0 ≤ q r)
    (hOp : ∀ r ∈ Ioo 0 R,
      0 ≤ -deriv (deriv u) r-11/r*deriv u r+(q r-V r)*u r) :
    ∀ r ∈ Icc 0 R, 0 ≤ u r := by
  let w := fun t : ℝ => Real.exp (t^2/24)*u t
  have hw : Differentiable ℝ w := fun r => (radialGaussian_product_deriv u hu r).differentiableAt
  have hw0 : deriv w 0=0 := by
    rw [(radialGaussian_product_deriv u hu 0).deriv,hu0]
    norm_num
  have hwR : 0 ≤ w R := mul_nonneg (Real.exp_pos _).le huR
  have hB : ∀ r ∈ Ioo 0 R, 0 < 11/r-r/6 := by
    intro r hr
    have hrsq : r^2 ≤ 11 := ((sq_le_sq₀ hr.1.le hR.le).2 hr.2.le).trans hR2
    apply sub_pos.mpr
    apply (lt_div_iff₀ hr.1).2
    nlinarith
  have hLap : ∀ r ∈ Ioo 0 R, w r < 0 →
      deriv (deriv w) r+(11/r-r/6)*deriv w r ≤ 0 := by
    intro r hr hwr
    rw [radialGaussian_operator_identity u hu r hr.1.ne' (hdu r hr)]
    have hur : u r < 0 := by
      by_contra! hu0
      exact (not_lt_of_ge (mul_nonneg (Real.exp_pos _).le hu0)) hwr
    have hrsq : r^2 ≤ 11 := ((sq_le_sq₀ hr.1.le hR.le).2 hr.2.le).trans hR2
    have hc : 0 < q r-V r+1-r^2/144 := by linarith [hq r hr,hV r hr]
    have hn := mul_neg_of_pos_of_neg hc hur
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    linarith [hOp r hr]
  have hpos := radial_minimum_principle_drift R 0 hR (fun r => 11/r-r/6)
    hB w hw hw0 hwR hLap
  intro r hr
  exact nonneg_of_mul_nonneg_right (hpos r hr) (Real.exp_pos (r^2/24))

end DefocusingNLS

end OAI
