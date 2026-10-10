import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedSmoothMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualMellinIntegral

namespace OAI

/-! Actual primary-selected additive Voronoi identity in every nonzero
angular type, prior to the finite cubic-character average. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

theorem cubicThetaSelected_voronoi_far (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A Z : ℝ} (hA : 1/2<A) (hZ : 0<Z) :
    cubicThetaSelectedAdditiveSum g rev k W Z=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*cubicThetaDualPrefactor (g 1 0)*
        ∑' n : MetaplecticDualArgument,
          (theta (cubicThetaCircleOrder rev k) n.val*
            cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
              (cubicThetaPrimaryDualCenter g) n.val)/
            (‖cubicThetaFrequency n.val‖:ℂ)*
            metaplecticTransform (cubicThetaCircleOrder (!rev) k) W A
              (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2) := by
  have hs := cubicThetaSelected_smooth_continued g hc rev hk W hW hpos hsm
    (σ:=2) (by norm_num) hZ
  have hc' := cubicThetaSelectedDirichlet_contour g hc rev hk W hW hpos hsm
    (a:= -A) (b:=2) (by linarith) hZ
  rw [←hc'] at hs
  let a : Eisenstein→ℂ := fun n => theta (cubicThetaCircleOrder rev k) n*
    cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc) (cubicThetaPrimaryDualCenter g) n
  let F (s : ℂ) : ℂ := mellin W s*(Z:ℂ)^s*(cubicThetaLevelScale (g 1 0):ℂ)^(4*s-2)*
    ((2*Real.pi:ℝ):ℂ)^(4*s-2)*metaplecticGammaQuotient (cubicThetaCircleOrder (!rev) k) s*
      cubicThetaDirichlet a (2*(1-s)-1)
  have he (t : ℝ) :
      mellin W ((-A:ℂ)+(t:ℂ)*Complex.I)*(Z:ℂ)^((-A:ℂ)+(t:ℂ)*Complex.I)*
        cubicThetaSelectedDirichlet g hc rev k ((-A:ℂ)+(t:ℂ)*Complex.I)=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*F ((-A:ℂ)+(t:ℂ)*Complex.I) := by
    have hkn : (0:ℝ)≤k := Nat.cast_nonneg k
    rw [cubicThetaSelectedDirichlet_gamma g hc rev hk (by simp; linarith)]
    rw [cubicThetaProjectedDirichlet_initial g hc rev hk (by simp; linarith)]
    dsimp only [F,a]
    ring
  have hd := cubicTheta_dual_mellin_integral (a := a) hc (by norm_num : (0:ℝ)≤243)
    (fun n => cubicTheta_twisted_angular_bound (by norm_num)
      (cubicThetaProjectedCoefficient_bound g hc) (cubicThetaPrimaryDualCenter g)
        (cubicThetaCircleOrder rev k) n)
    (cubicThetaCircleOrder (!rev) k) W hW hpos hsm hA hZ
  calc
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∫ t : ℝ,
        (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*F ((-A:ℂ)+(t:ℂ)*Complex.I)) := by
      rw [hs]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simpa only [Complex.ofReal_neg] using he t
    _ = (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*
        (((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,F ((-A:ℂ)+(t:ℂ)*Complex.I)) := by
      rw [integral_const_mul]
      ring
    _ = _ := by rw [show (((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
        F ((-A:ℂ)+(t:ℂ)*Complex.I))=_ from hd]; ring

end CubicFirstMoment

end

end OAI
