import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialSmoothMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualMellinIntegral
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShiftedVoronoi

namespace OAI

/-! The actual radial primary-selected Voronoi formula. Its pole term
contains the residue computed from the actual arithmetic theta section. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

theorem cubicThetaSelected_radial_voronoi_far (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {A Z : ℝ} (hA : 1/2<A) (hZ : 0<Z) :
    cubicThetaSelectedAdditiveSum g false 0 W Z=
      cubicThetaDualPrefactor (g 1 0)*∑' n : MetaplecticDualArgument,
        cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
          (cubicThetaPrimaryDualCenter g) n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
          metaplecticTransform 0 W A (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2)+
      cubicThetaSelectedRadialResidue g hc*mellin W (5/6)*(Z:ℂ)^(5/6:ℂ) := by
  rw [cubicThetaSelected_smooth_radial_shift g hc W hW hpos hsm
    (a:= -A) (by linarith) hZ]
  congr 1
  let a := cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
    (cubicThetaPrimaryDualCenter g)
  have hd := cubicTheta_dual_mellin_integral (a:=a) hc (by norm_num : (0:ℝ) ≤ 243)
    (fun n => by rw [cubicThetaCoefficientTwist_norm]; exact cubicThetaProjectedCoefficient_bound g hc n)
    0 W hW hpos hsm hA hZ
  convert hd using 2
  apply integral_congr_ae
  filter_upwards with t
  rw [cubicThetaSelectedRadialDirichlet_functional g hc (by simp; linarith),
    cubicThetaProjectedRadialDirichlet_initial g hc (by simp; linarith)]
  simp only [Complex.ofReal_neg]
  dsimp only [a]
  ring

theorem cubicThetaSelected_radial_voronoi (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W⊆Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ Z : ℝ} (hσ : 0<σ) (hZ : 0<Z) :
    Summable (fun n : MetaplecticDualArgument =>
      cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
        (cubicThetaPrimaryDualCenter g) n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
        metaplecticTransform 0 W σ (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2)) ∧
    cubicThetaSelectedAdditiveSum g false 0 W Z=
      cubicThetaDualPrefactor (g 1 0)*∑' n : MetaplecticDualArgument,
        cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
          (cubicThetaPrimaryDualCenter g) n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
          metaplecticTransform 0 W σ (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2)+
      cubicThetaSelectedRadialResidue g hc*mellin W (5/6)*(Z:ℂ)^(5/6:ℂ) := by
  let A := σ+1
  let T (s : ℝ) (n : MetaplecticDualArgument) : ℂ :=
    cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
      (cubicThetaPrimaryDualCenter g) n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
        metaplecticTransform 0 W s (cubicThetaDualScale (g 1 0) Z*‖cubicThetaFrequency n.val‖^2)
  have hA : 1/2<A := by dsimp [A]; linarith
  have hT : T σ=T A := by
    funext n
    dsimp only [T]
    rw [metaplecticTransform_line_eq 0 W hW hpos hsm hσ (by dsimp [A]; linarith : σ ≤ A)
      (mul_pos (cubicThetaDualScale_pos hc hZ) (sq_pos_of_pos (cubicThetaFrequency_pos n.property)))
      (angularGammaQuotientStripBound_proved _ _ (by norm_num [metaplecticAngularShift]))
      (angularGammaQuotientStripBound_proved _ _ (by norm_num [metaplecticAngularShift]))]
  have hs : Summable (T A) := cubicTheta_dual_mellin_summable hc (by norm_num : (0:ℝ) ≤ 243)
    (fun n => by rw [cubicThetaCoefficientTwist_norm]; exact cubicThetaProjectedCoefficient_bound g hc n)
    0 W hW hpos hsm hA hZ
  refine ⟨?_,?_⟩
  · change Summable (T σ)
    rwa [hT]
  · change cubicThetaSelectedAdditiveSum g false 0 W Z=
      cubicThetaDualPrefactor (g 1 0)*∑' n,T σ n+_
    rw [hT]
    exact cubicThetaSelected_radial_voronoi_far g hc W hW hpos hsm hA hZ

end CubicFirstMoment

end

end OAI
