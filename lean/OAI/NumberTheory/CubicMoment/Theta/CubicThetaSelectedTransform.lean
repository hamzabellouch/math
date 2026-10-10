import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSelectedVoronoi
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShiftedVoronoi

namespace OAI

/-! The actual primary-selected angular transform on every negative line,
with absolute convergence inherited from its proved far-left formula. -/
noncomputable section
open Set
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

theorem cubicThetaSelected_voronoi (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ Z : ℝ} (hσ : 0<σ) (hZ : 0<Z) :
    Summable (fun n : MetaplecticDualArgument =>
      (theta (cubicThetaCircleOrder rev k) n.val*
        cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
          (cubicThetaPrimaryDualCenter g) n.val)/(‖cubicThetaFrequency n.val‖:ℂ)*
        metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
          (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2)) ∧
    cubicThetaSelectedAdditiveSum g rev k W Z=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*cubicThetaDualPrefactor (g 1 0)*
        ∑' n : MetaplecticDualArgument,
          (theta (cubicThetaCircleOrder rev k) n.val*
            cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
              (cubicThetaPrimaryDualCenter g) n.val)/(‖cubicThetaFrequency n.val‖:ℂ)*
            metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
              (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2) := by
  let A := σ+1
  let T (s : ℝ) (n : MetaplecticDualArgument) : ℂ :=
    (theta (cubicThetaCircleOrder rev k) n.val*
      cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
        (cubicThetaPrimaryDualCenter g) n.val)/(‖cubicThetaFrequency n.val‖:ℂ)*
      metaplecticTransform (cubicThetaCircleOrder (!rev) k) W s
        (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2)
  have hA : 1/2<A := by dsimp [A]; linarith
  have hT : T σ=T A := by
    funext n
    dsimp only [T]
    rw [metaplecticTransform_line_eq (cubicThetaCircleOrder (!rev) k) W hW hpos hsm hσ
      (by dsimp [A]; linarith : σ≤A)
      (mul_pos (cubicThetaDualScale_pos hc hZ) (sq_pos_of_pos (cubicThetaFrequency_pos n.property)))
      (angularGammaQuotientStripBound_proved _ _ (by
        linarith [metaplecticAngularShift_nonneg (cubicThetaCircleOrder (!rev) k)]))
      (angularGammaQuotientStripBound_proved _ _ (by
        linarith [metaplecticAngularShift_nonneg (cubicThetaCircleOrder (!rev) k)]))]
  have hs : Summable (T A) := cubicTheta_dual_mellin_summable hc (by norm_num : (0:ℝ)≤243)
    (fun n => cubicTheta_twisted_angular_bound (by norm_num)
      (cubicThetaProjectedCoefficient_bound g hc) (cubicThetaPrimaryDualCenter g)
        (cubicThetaCircleOrder rev k) n)
    (cubicThetaCircleOrder (!rev) k) W hW hpos hsm hA hZ
  have he := cubicThetaSelected_voronoi_far g hc rev hk W hW hpos hsm hA hZ
  change Summable (T σ) ∧ _
  constructor
  · rwa [hT]
  · change cubicThetaSelectedAdditiveSum g rev k W Z=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*cubicThetaDualPrefactor (g 1 0)*∑' n,T σ n
    rw [hT]
    exact he

end CubicFirstMoment

end

end OAI
