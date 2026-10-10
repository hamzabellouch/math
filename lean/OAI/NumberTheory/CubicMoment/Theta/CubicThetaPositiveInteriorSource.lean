import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeInteriorFourier

namespace OAI

/-! Exact inward/outward recurrence of actual Fourier sources at every
positive cutoff. All radial changes retain the hyperbolic Jacobian. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

theorem cubicThetaPositiveInteriorSource {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaPrimeCubeHeckeMass hp (cubicThetaPositiveFourierMass (p^3*h) W hε hW hsm)=
      (((‖(p:ℂ)‖^3)^2:ℝ):ℂ) •
        cubicThetaPositiveFourierMass h
          (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)⁻¹
            (inv_pos.mpr (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3)) W)
          (div_pos hε (inv_pos.mpr (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3)))
          (cubicThetaRadialWeightScale_positive_low _ W hW)
          (cubicThetaRadialWeightScale_smooth _ _ W hsm)+
      cubicThetaPositiveFourierMass (p^3*(p^3*h))
        (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
          (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) W)
        (div_pos hε (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3))
        (cubicThetaRadialWeightScale_positive_low _ W hW)
        (cubicThetaRadialWeightScale_smooth _ _ W hsm) := by
  let r := ‖(p:ℂ)‖^3
  have hr : 0<r := pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3
  apply ext_inner_right ℂ
  intro v
  refine cubicThetaFiniteMassClosure_dense.induction_on v
    (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro F
  rw [←cubicThetaPrimeCubeHeckeMass_symmetric,cubicThetaPrimeCubeHeckeMass_finite,
    cubicThetaPositiveFourierMass_pairing_finite,inner_add_left]
  rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaAutomorphicL2)]
  simp only [starRingEnd_apply]
  have hfun (v : ℝ) (hv : 0<v) :
      cubicThetaSectionFourierFunction (cubicThetaPrimeCubeHeckeFinite hp F) (p^3*h) v=
        cubicThetaSectionFourierFunction F h (r*v)+
          (norm (p^3):ℂ)*cubicThetaSectionFourierFunction F (p^3*(p^3*h)) (v/r) := by
    rw [cubicThetaSectionFourierFunction_eq _ _ _ hv]
    change cubicThetaSectionFourier (cubicThetaPrimeCubeHecke hp F) v hv (p^3*h)=_
    rw [cubicThetaPrimeCubeHecke_fourier_interior hp F v hv h,
      cubicThetaSectionFourierFunction_eq _ _ _ (mul_pos hr hv),
      cubicThetaSectionFourierFunction_eq _ _ _ (div_pos hv hr)]
  have hN : (norm (p^3):ℂ)=(r:ℂ)^2 := by
    rw [cubicThetaPrimeCube_norm_power]
    dsimp only [r]
    push_cast
    ring
  have hA := cubicThetaPositiveFourier_dilate_integrable F h hr W hε hW
  have hB := cubicThetaPositiveFourier_divide_integrable F (p^3*(p^3*h)) hr W hε hW
  calc
    _ = (∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h (r*v))+
        (norm (p^3):ℂ)*(∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*
          cubicThetaSectionFourierFunction F (p^3*(p^3*h)) (v/r)) := by
      rw [←integral_const_mul,←integral_add hA (hB.const_mul _)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [hfun v hv]
      ring
    _ = _ := by
      rw [cubicThetaPositiveFourier_dilate_pairing F h hr W hε hW hsm,
        cubicThetaPositiveFourier_divide_pairing F (p^3*(p^3*h)) hr W hε hW hsm,hN]
      have hrC : (r:ℂ)^2≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')
      rw [←mul_assoc, mul_inv_cancel₀ hrC,one_mul]
      push_cast
      simp only [r,star_pow,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_pow]

end CubicFirstMoment

end

end OAI
