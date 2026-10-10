import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSquareFourier

namespace OAI

/-! The square-class source identity holds for every positive cutoff,
including the lower profiles reached by repeated Hecke action. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

theorem cubicThetaPositiveSquareSource {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaPrimeCubeHeckeMass hp (cubicThetaPositiveFourierMass (p^2*h) W hε hW hsm)=
      cubicThetaPositiveFourierMass (p^3*(p^2*h))
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
    cubicThetaPositiveFourierMass_pairing_finite]
  have hf (v : ℝ) (hv : 0<v) :
      cubicThetaSectionFourierFunction (cubicThetaPrimeCubeHeckeFinite hp F) (p^2*h) v=
        (norm (p^3):ℂ)*cubicThetaSectionFourierFunction F (p^3*(p^2*h)) (v/r) := by
    rw [cubicThetaSectionFourierFunction_eq _ _ _ hv]
    change cubicThetaSectionFourier (cubicThetaPrimeCubeHecke hp F) v hv (p^2*h)=_
    rw [cubicThetaPrimeCubeHecke_fourier_square hp F v hv h hh,
      cubicThetaSectionFourierFunction_eq _ _ _ (div_pos hv hr)]
  have hN : (norm (p^3):ℂ)=(r:ℂ)^2 := by
    rw [cubicThetaPrimeCube_norm_power]
    dsimp only [r]
    push_cast
    ring
  calc
    _ = (norm (p^3):ℂ)*(∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*
        cubicThetaSectionFourierFunction F (p^3*(p^2*h)) (v/r)) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [hf v hv]
      ring
    _ = _ := by
      rw [cubicThetaPositiveFourier_divide_pairing F (p^3*(p^2*h)) hr W hε hW hsm,hN]
      have hrC : (r:ℂ)^2≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')
      rw [←mul_assoc,mul_inv_cancel₀ hrC,one_mul]

end CubicFirstMoment

end

end OAI
