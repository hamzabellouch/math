import OAI.NumberTheory.CubicMoment.Estimates.CubeRiesz
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialLattice

namespace OAI

/-! Put the proved cube Riesz integral in the same radial Mellin
normalization as the squarefree lattice density. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma integral_radial_third_weight (W : ℝ → ℂ) :
    (∫ x in Ioi (0:ℝ), ((x^(-1/3:ℝ):ℝ):ℂ)*W x) = mellin W (2/3) := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Complex.ofReal_cpow hx.le]
  norm_num

lemma integral_plane_third_weight (W : ℝ → ℂ) :
    (∫ z : ℂ, ((‖z‖^(-2/3:ℝ):ℝ):ℂ)*W (Complex.normSq z)) =
      (Real.pi:ℂ)*mellin W (2/3) := by
  calc
    _ = ∫ z : ℂ, (((Complex.normSq z)^(-1/3:ℝ):ℝ):ℂ)*W (Complex.normSq z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [Complex.normSq_eq_norm_sq,←Real.rpow_natCast ‖z‖ 2,
        ←Real.rpow_mul (_root_.norm_nonneg z)]
      norm_num
    _ = (Real.pi:ℂ)*(∫ x in Ioi (0:ℝ), ((x^(-1/3:ℝ):ℝ):ℂ)*W x) :=
      integral_normSq_profile (fun x => ((x^(-1/3:ℝ):ℝ):ℂ)*W x)
    _ = _ := by rw [integral_radial_third_weight]

theorem cubeProfileIntegral_eq_mellin (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) :
    cubeProfileIntegral W = ((cStar^2*(2*Real.pi/Real.sqrt 3):ℝ):ℂ)*mellin W (2/3) := by
  rw [cubeProfileIntegral_eq_model W hW hW']
  simp_rw [show -(2/3:ℝ) = -2/3 by ring]
  rw [integral_plane_third_weight]
  simp only [Complex.real_smul]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
