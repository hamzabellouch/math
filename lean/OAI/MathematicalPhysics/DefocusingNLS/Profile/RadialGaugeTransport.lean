import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGaugeLinearization
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianDeformation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorVelocity

namespace OAI

/-! Identification of the gauged transport with the actual positive radial field. -/

open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialComplex_fderiv (q : ℝ → ℂ) (x v : E) (hx : x≠0)
    (hq : DifferentiableAt ℝ q ‖x‖) :
    fderiv ℝ (fun y : E => q ‖y‖) x v=
      ((inner ℝ x v/‖x‖ : ℝ) : ℂ)*deriv q ‖x‖ := by
  have hn := (contDiffAt_norm ℝ hx (n := 1)).differentiableAt one_ne_zero
  have hd := hq.hasFDerivAt.comp x hn.hasFDerivAt
  change HasFDerivAt (fun y : E => q ‖y‖) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,fderiv_eq_smul_deriv,
    Complex.real_smul]
  rw [radial_norm_fderiv_apply x v hx]

theorem radialComplex_fderiv_zero (q : ℝ → ℂ)
    (hq : DifferentiableAt ℝ (fun y : E => q ‖y‖) 0) :
    fderiv ℝ (fun y : E => q ‖y‖) 0=0 := by
  let f : E → ℂ := fun y => q ‖y‖
  have hq' : HasFDerivAt f (fderiv ℝ f 0) ((-id) (0 : E)) := by
    simpa only [Pi.neg_apply,id_eq,neg_zero] using hq.hasFDerivAt
  have hn := hq'.comp (0 : E) ((hasFDerivAt_id (0 : E)).neg)
  have he : (fun y : E => f (-y))=f := by
    funext y
    simp [f]
  change HasFDerivAt (fun y => f (-y)) _ 0 at hn
  rw [he] at hn
  have hd := congrArg (fun L : E →L[ℝ] ℂ => L) hn.fderiv
  ext v
  have hv := congrArg (fun L : E →L[ℝ] ℂ => L v) hd
  simp only [ContinuousLinearMap.comp_apply,neg_apply,ContinuousLinearMap.id_apply,
    map_neg] at hv
  change fderiv ℝ f 0 v=0
  linear_combination hv/2

theorem basis_inner_derivative_sum (u : E → ℂ) (x : E) :
    (∑ j : Fin 12, ((inner ℝ x (EuclideanSpace.basisFun (Fin 12) ℝ j) : ℝ) : ℂ)*
      fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j))=fderiv ℝ u x x := by
  have he := congrArg (fderiv ℝ u x) ((EuclideanSpace.basisFun (Fin 12) ℝ).sum_repr' x)
  simpa only [map_sum,map_smul,Complex.real_smul,real_inner_comm] using he

theorem radialMatched_gaugeTransport (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (u : E → ℂ) (x : E) :
    gaugeTransport (radialMatchedCartesian n z) u x=
      fderiv ℝ u x (radialMatchedVectorField n z x) := by
  let Q := radialMatchedProfile n z
  by_cases hx : x=0
  · subst x
    have hd := radialComplex_fderiv_zero Q
      ((radialMatchedCartesian_contDiff n z hX hz).differentiable (by simp) 0)
    change fderiv ℝ (radialMatchedCartesian n z) 0=0 at hd
    simp [gaugeTransport,hd,radialMatchedVectorField]
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hd (v : E) : fderiv ℝ (radialMatchedCartesian n z) x v=
        ((inner ℝ x v/‖x‖ : ℝ) : ℂ)*deriv Q ‖x‖ :=
      radialComplex_fderiv Q x v hx (radialMatchedProfile_differentiable n z hX hz ‖x‖)
    have hcoef (j : Fin 12) :
        ((fderiv ℝ (radialMatchedCartesian n z) x
          (EuclideanSpace.basisFun (Fin 12) ℝ j)/radialMatchedCartesian n z x).im : ℝ)=
        (deriv Q ‖x‖/Q ‖x‖).im/‖x‖*
          inner ℝ x (EuclideanSpace.basisFun (Fin 12) ℝ j) := by
      rw [hd]
      change ((((inner ℝ x _/‖x‖ : ℝ) : ℂ)*deriv Q ‖x‖)/Q ‖x‖).im=_
      rw [mul_div_assoc]
      simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      ring
    have hs : (∑ j : Fin 12,
        (((fderiv ℝ (radialMatchedCartesian n z) x
          (EuclideanSpace.basisFun (Fin 12) ℝ j)/radialMatchedCartesian n z x).im : ℝ) : ℂ)*
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin 12) ℝ j))=
        (((deriv Q ‖x‖/Q ‖x‖).im/‖x‖ : ℝ) : ℂ)*fderiv ℝ u x x := by
      simp_rw [hcoef,Complex.ofReal_mul,mul_assoc]
      rw [← Finset.mul_sum,basis_inner_derivative_sum]
    have hw := radialMatchedVelocity_formula n z hX hz ‖x‖ hr
    rw [mul_div_assoc,← complex_logDerivative_im] at hw
    change ‖x‖/2+2*(deriv Q ‖x‖/Q ‖x‖).im=
      ‖x‖*radialVelocityRatio (6-2*radialShootingA n) (fun r => ‖Q r‖) ‖x‖ at hw
    have hratio : (1/2 : ℝ)+2*((deriv Q ‖x‖/Q ‖x‖).im/‖x‖)=
        radialVelocityRatio (6-2*radialShootingA n) (fun r => ‖Q r‖) ‖x‖ := by
      apply (mul_left_cancel₀ hr.ne')
      convert hw using 1
      field_simp
    unfold gaugeTransport
    rw [hs]
    simp only [radialMatchedVectorField,map_smul,Complex.real_smul]
    rw [← hratio]
    push_cast
    ring

end DefocusingNLS

end OAI
