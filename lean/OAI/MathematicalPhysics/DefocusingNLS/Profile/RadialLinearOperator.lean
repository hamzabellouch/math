import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLinearComparison

namespace OAI

/-! Linearity and order comparison for the scalar radial operator. -/

open Set
namespace DefocusingNLS

noncomputable def radialLinearOperator (V q u : ℝ → ℝ) (r : ℝ) : ℝ :=
  -deriv (deriv u) r-11/r*deriv u r+(q r-V r)*u r

theorem radialLinearOperator_sub (V q u v : ℝ → ℝ)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (r : ℝ)
    (hdu : DifferentiableAt ℝ (deriv u) r) (hdv : DifferentiableAt ℝ (deriv v) r) :
    radialLinearOperator V q (u-v) r=
      radialLinearOperator V q u r-radialLinearOperator V q v r := by
  have hd : deriv (u-v)=fun t => deriv u t-deriv v t := by
    funext t
    exact ((hu t).hasDerivAt.sub (hv t).hasDerivAt).deriv
  have hdd : deriv (deriv (u-v)) r=deriv (deriv u) r-deriv (deriv v) r := by
    rw [hd]
    exact (hdu.hasDerivAt.sub hdv.hasDerivAt).deriv
  unfold radialLinearOperator
  rw [hdd,hd]
  dsimp only [Pi.sub_apply]
  ring

theorem radialLinearOperator_const_mul (V q u : ℝ → ℝ) (c r : ℝ) :
    radialLinearOperator V q (fun t => c*u t) r=c*radialLinearOperator V q u r := by
  have hd : deriv (fun t => c*u t)=fun t => c*deriv u t := by
    funext t
    exact deriv_const_mul_field c
  unfold radialLinearOperator
  rw [hd,deriv_const_mul_field]
  dsimp only
  ring

theorem radialLinearOperator_compare (R : ℝ) (hR : 0 < R) (hR2 : R^2 ≤ 11)
    (V q u v : ℝ → ℝ) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (hdu : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv u) r)
    (hdv : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv v) r)
    (hu0 : deriv u 0=0) (hv0 : deriv v 0=0) (hb : u R ≤ v R)
    (hV : ∀ r ∈ Ioo 0 R, V r ≤ (1/2 : ℝ))
    (hq : ∀ r ∈ Ioo 0 R, 0 ≤ q r)
    (hL : ∀ r ∈ Ioo 0 R, radialLinearOperator V q u r ≤ radialLinearOperator V q v r) :
    ∀ r ∈ Icc 0 R, u r ≤ v r := by
  have hd : deriv (v-u)=fun t => deriv v t-deriv u t := by
    funext t
    exact ((hv t).hasDerivAt.sub (hu t).hasDerivAt).deriv
  have hd2 : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv (v-u)) r := by
    intro r hr
    rw [hd]
    exact (hdv r hr).sub (hdu r hr)
  have hd0 : deriv (v-u) 0=0 := by
    rw [hd]
    change deriv v 0-deriv u 0=0
    rw [hu0,hv0,sub_self]
  have hOp : ∀ r ∈ Ioo 0 R, 0 ≤ radialLinearOperator V q (v-u) r := by
    intro r hr
    rw [radialLinearOperator_sub V q v u hv hu r (hdv r hr) (hdu r hr)]
    exact sub_nonneg.2 (hL r hr)
  have h := radial_linear_comparison R hR hR2 (v-u) V q (hv.sub hu) hd2 hd0
    (sub_nonneg.2 hb) hV hq hOp
  intro r hr
  exact sub_nonneg.1 (h r hr)

theorem radialLinearOperator_abs_bound (R M : ℝ) (hR : 0 < R) (hR2 : R^2 ≤ 11)
    (hM : 0 ≤ M) (V q u S : ℝ → ℝ) (hu : Differentiable ℝ u) (hS : Differentiable ℝ S)
    (hdu : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv u) r)
    (hdS : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv S) r)
    (hu0 : deriv u 0=0) (hS0 : deriv S 0=0) (huR : u R=0) (hSR : 0 ≤ S R)
    (hV : ∀ r ∈ Ioo 0 R, V r ≤ (1/2 : ℝ))
    (hq : ∀ r ∈ Ioo 0 R, 0 ≤ q r)
    (hLu : ∀ r ∈ Ioo 0 R, |radialLinearOperator V q u r| ≤ M)
    (hLS : ∀ r ∈ Ioo 0 R, 1 ≤ radialLinearOperator V q S r) :
    ∀ r ∈ Icc 0 R, |u r| ≤ M*S r := by
  have hMS : Differentiable ℝ (fun t => M*S t) := hS.const_mul M
  have hdMS : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv (fun t => M*S t)) r := by
    intro r hr
    have hd : deriv (fun t => M*S t)=fun t => M*deriv S t := by
      funext t
      exact deriv_const_mul_field M
    rw [hd]
    exact (hdS r hr).const_mul M
  have hMS0 : deriv (fun t => M*S t) 0=0 := by rw [deriv_const_mul_field,hS0,mul_zero]
  have hMSR : 0 ≤ M*S R := mul_nonneg hM hSR
  have hUp : ∀ r ∈ Icc 0 R, u r ≤ M*S r :=
    radialLinearOperator_compare R hR hR2 V q u (fun t => M*S t) hu hMS hdu hdMS hu0 hMS0
      (by rw [huR]; exact hMSR) hV hq (by
        intro r hr
        rw [radialLinearOperator_const_mul]
        exact (le_abs_self _).trans ((hLu r hr).trans (by nlinarith [hLS r hr])))
  have hNeg0 : deriv (fun t => -u t) 0=0 := by
    have h := deriv.neg (f := u) (x := (0 : ℝ))
    change deriv (fun t => -u t) 0= -deriv u 0 at h
    simpa only [hu0,neg_zero] using h
  have hdNeg : ∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv (fun t => -u t)) r := by
    intro r hr
    have hd : deriv (fun t => -u t)=fun t => -deriv u t := by ext t; exact deriv.neg
    rw [hd]
    exact (hdu r hr).neg
  have hDown : ∀ r ∈ Icc 0 R, -u r ≤ M*S r :=
    radialLinearOperator_compare R hR hR2 V q (fun t => -u t) (fun t => M*S t) hu.neg hMS
      hdNeg hdMS hNeg0 hMS0 (by rw [huR,neg_zero]; exact hMSR) hV hq (by
        intro r hr
        have he : radialLinearOperator V q (fun t => -u t) r= -radialLinearOperator V q u r := by
          simpa only [neg_one_mul] using radialLinearOperator_const_mul V q u (-1) r
        rw [he,radialLinearOperator_const_mul]
        exact (neg_le_abs _).trans ((hLu r hr).trans (by nlinarith [hLS r hr])))
  intro r hr
  exact abs_le.2 ⟨by linarith [hDown r hr],hUp r hr⟩

end DefocusingNLS

end OAI
