import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualPhase

namespace OAI

/-! The numerical and Gauss factors in the constructed transform. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaDualPrefactor_eq {r : Eisenstein} (hr : primary r) :
    cubicThetaDualPrefactor r=(norm r:ℂ)/((2*Real.pi:ℝ):ℂ)^2 := by
  have hsq := cubicThetaLevelScale_square r
  have hR : (norm r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero (primary_ne_zero hr)).ne'
  unfold cubicThetaDualPrefactor
  rw [show (-2:ℂ)=((-2:ℤ):ℂ) by norm_num,Complex.cpow_intCast,
    Complex.cpow_intCast]
  simp only [zpow_neg,zpow_ofNat,←Complex.ofReal_pow,hsq,Complex.ofReal_inv,inv_inv]
  rw [div_eq_mul_inv]

lemma cubicThetaGauss_square {r : Eisenstein} (hr : primary r) (hs : Squarefree r) :
    ((Real.sqrt (norm r):ℂ)*gauss r)*star ((Real.sqrt (norm r):ℂ)*gauss r)=(norm r:ℂ) := by
  rw [mul_assoc,gauss_mul_conj_unnormalized hr hs,←Complex.ofReal_mul]
  congr 1
  nlinarith [Real.sq_sqrt (norm_nonneg r)]

lemma cubicThetaDual_scalar {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (rev : Bool) (k : ℕ) :
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*(81*metaplecticRawPrefactor r (cubicThetaCircleOrder (!rev) k))=
    (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      (27*theta (cubicThetaCircleOrder rev k) lambdaE) := by
  have hthree : (3:ℝ)^(7/2:ℝ)=3*(3:ℝ)^(5/2:ℝ) := by
    rw [show (7/2:ℝ)=1+5/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_one]
  have hphase := cubicTheta_root_phase hr rev k
  have hrearrange : (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      (27*theta (cubicThetaCircleOrder rev k) lambdaE)=
    (theta (cubicThetaCircleOrder (!rev) k) lambdaE*
      (star (r:ℂ)/(r:ℂ))^(-cubicThetaCircleOrder (!rev) k))*(27*cubicThetaDualPrefactor r) := by
    rw [←hphase]
    ring
  rw [hrearrange,cubicThetaDualPrefactor_eq hr]
  unfold metaplecticRawPrefactor
  calc
    _ = ((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE*
      (81*(norm r:ℂ))/((3^(7/2:ℝ)*(2*Real.pi)^2:ℝ):ℂ)*
        (star (r:ℂ)/(r:ℂ))^(-cubicThetaCircleOrder (!rev) k) := by
      rw [←cubicThetaGauss_square hr hs]
      ring
    _ = _ := by
      rw [hthree]
      push_cast
      field_simp
      ring

end CubicFirstMoment

end

end OAI
