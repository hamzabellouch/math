import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSmallInverse

namespace OAI

/-! The small radial inverse estimate with a nonzero Dirichlet boundary value. -/

open Set
namespace DefocusingNLS

theorem radial_small_inverse_boundary_bound (p : ℕ) (hp : 10 ≤ p) (R M E : ℝ)
    (hR : 1 ≤ R) (hR2 : R^2 ≤ 11) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (V q u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hdu : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv u) r)
    (hu0 : deriv u 0=0) (huR : |u R| ≤ E)
    (hV : ∀ r ∈ Ioo 0 R, V r ≤ (1/2 : ℝ))
    (hq : ∀ r ∈ Ioo 0 R, 0 ≤ q r)
    (hcore : ∀ r ∈ Ioo 0 R, r ≤ R-7/10000 → (p : ℝ)/5 ≤ q r)
    (hLu : ∀ r ∈ Ioo 0 R, |radialLinearOperator V q u r| ≤ M) :
    ∀ r ∈ Icc 0 R, |u r| ≤ E+(M+E/2)*(10/(p : ℝ)+(8/10000 : ℝ)^2) := by
  let S := radialSmallInverseBarrier p R
  let c := M+E/2
  let W := fun r => E+c*S r
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hS : Differentiable ℝ S :=
    differentiable_radialInverseBarrier _ _ _ _ (by norm_num)
  have hdS : ∀ r, DifferentiableAt ℝ (deriv S) r :=
    fun r => differentiable_deriv_radialInverseBarrier _ _ _ _ (by norm_num) r
  have hW : Differentiable ℝ W := (hS.const_mul c).const_add E
  have hdW : deriv W=fun r => c*deriv S r := by
    funext r
    change deriv (fun t => E+c*S t) r=_
    rw [deriv_const_add,deriv_const_mul_field]
  have hddW : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv W) r := by
    intro r _
    rw [hdW]
    exact (hdS r).const_mul c
  have hW0 : deriv W 0=0 := by
    rw [hdW]
    change c*deriv (radialSmallInverseBarrier p R) 0=0
    rw [radialSmallInverseBarrier_origin p R hR,mul_zero]
  have hOp (r : ℝ) (hr : r ∈ Ioo 0 R) : M ≤ radialLinearOperator V q W r := by
    have hid : radialLinearOperator V q W r=(q r-V r)*E+c*radialLinearOperator V q S r := by
      unfold radialLinearOperator
      rw [hdW,deriv_const_mul_field]
      change -(c*deriv (deriv S) r)-11/r*(c*deriv S r)+(q r-V r)*(E+c*S r)=_
      ring
    rw [hid]
    have hs := radialSmallInverseBarrier_supersolution p hp R V q hV hq hcore r hr
    have he : -(E/2) ≤ (q r-V r)*E := by nlinarith [hV r hr,hq r hr]
    have hh : c ≤ c*radialLinearOperator V q S r := by
      exact le_mul_of_one_le_right hc hs
    calc
      M = -(E/2)+c := by dsimp [c]; ring
      _ ≤ _ := add_le_add he hh
  have hWR : E ≤ W R := by
    have hS0 : 0 ≤ S R := (by positivity : 0 ≤ 10/(p : ℝ)).trans
      (radialSmallInverseBarrier_bounds p R R ⟨by linarith,le_rfl⟩).1
    dsimp [W]
    exact le_add_of_nonneg_right (mul_nonneg hc hS0)
  have hup : ∀ r ∈ Icc 0 R, u r ≤ W r :=
    radialLinearOperator_compare R (by linarith) hR2 V q u W hu hW hdu hddW hu0 hW0
      ((le_abs_self _).trans (huR.trans hWR)) hV hq
      (fun r hr => (le_abs_self _).trans ((hLu r hr).trans (hOp r hr)))
  have hneg0 : deriv (fun r => -u r) 0=0 := by
    have hh : deriv (fun r => -u r) 0= -deriv u 0 := deriv.neg
    simpa only [hu0,neg_zero] using hh
  have hdneg : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv (fun r => -u r)) r := by
    intro r hr
    have he : deriv (fun t => -u t)=fun t => -deriv u t := by funext t; exact deriv.neg
    rw [he]
    exact (hdu r hr).neg
  have hdown : ∀ r ∈ Icc 0 R, -u r ≤ W r :=
    radialLinearOperator_compare R (by linarith) hR2 V q (fun r => -u r) W hu.neg hW hdneg hddW
      hneg0 hW0 ((neg_le_abs _).trans (huR.trans hWR)) hV hq (by
        intro r hr
        have he : radialLinearOperator V q (fun r => -u r) r= -radialLinearOperator V q u r := by
          simpa only [neg_one_mul] using radialLinearOperator_const_mul V q u (-1) r
        rw [he]
        exact (neg_le_abs _).trans ((hLu r hr).trans (hOp r hr)))
  intro r hr
  have hbound : |u r| ≤ W r := abs_le.mpr ⟨by linarith [hdown r hr],hup r hr⟩
  apply hbound.trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (radialSmallInverseBarrier_bounds p R r hr).2 hc)

end DefocusingNLS

end OAI
