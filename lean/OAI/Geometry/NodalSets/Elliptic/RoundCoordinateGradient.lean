import OAI.Geometry.NodalSets.Charts.SphereChartConformal
import OAI.Geometry.NodalSets.Coefficients.GlobalCorrection
import OAI.Geometry.NodalSets.Elliptic.SeedCoordinateField

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

def roundCoordFactor (x : Yau.Jets.Coord) : ℝ := ((‖seedCoordEquiv x‖^2+4)/4)^2

def roundCoordGradient (u : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) : ℝ :=
  roundCoordFactor x * fderiv ℝ u x (Pi.single i 1)

lemma roundCoordFactor_ge_one (x : Yau.Jets.Coord) : 1 ≤ roundCoordFactor x := by
  unfold roundCoordFactor
  nlinarith [sq_nonneg (‖seedCoordEquiv x‖)]

lemma roundCoordFactor_smooth : ContDiff ℝ ∞ roundCoordFactor := by
  unfold roundCoordFactor
  exact ((((contDiff_norm_sq ℝ).comp seedCoordEquiv.contDiff).add contDiff_const).div_const 4).pow 2

lemma roundCoordGradient_smooth (u : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (roundCoordGradient u) := by
  apply contDiff_pi.mpr
  intro i
  exact roundCoordFactor_smooth.mul ((hu.fderiv_right (by simp)).clm_apply contDiff_const)

lemma coord_covector_sum (L : Yau.Jets.Coord →L[ℝ] ℝ) (v : Yau.Jets.Coord) :
    (∑ i, L (Pi.single i 1)*v i) = L v := by
  have hv : v = ∑ i : Fin 4, v i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hv]
  simp [mul_comm]

lemma roundCoordGradient_pair (u : Yau.Jets.Coord → ℝ) (x v : Yau.Jets.Coord) :
    ⟪sphereChartDerivative seedPoint (seedCoordEquiv x) (seedCoordEquiv (roundCoordGradient u x)),
      sphereChartDerivative seedPoint (seedCoordEquiv x) (seedCoordEquiv v)⟫ =
      fderiv ℝ u x v := by
  rw [sphereChartDerivative_conformal]
  have hi : ⟪seedCoordEquiv (roundCoordGradient u x),seedCoordEquiv v⟫ =
      roundCoordFactor x * fderiv ℝ u x v := by
    change (∑ i, v i * (roundCoordFactor x*fderiv ℝ u x (Pi.single i 1))) = _
    rw [← coord_covector_sum (fderiv ℝ u x) v,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hi]
  have hn : ‖seedCoordEquiv x‖^2+4 ≠ 0 := by positivity
  unfold roundCoordFactor
  field_simp

lemma roundCoordGradient_energy (u : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    ⟪sphereChartDerivative seedPoint (seedCoordEquiv x) (seedCoordEquiv (roundCoordGradient u x)),
      sphereChartDerivative seedPoint (seedCoordEquiv x) (seedCoordEquiv (roundCoordGradient u x))⟫ =
      roundCoordFactor x * (sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1)))^2 := by
  rw [roundCoordGradient_pair,← coord_covector_sum (fderiv ℝ u x) (roundCoordGradient u x)]
  rw [sourceEuclideanNorm,Real.sq_sqrt (by positivity),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [roundCoordGradient]
  ring

lemma roundCoordGradient_pairing (u : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    Yau.pairing u (roundCoordGradient u) x =
      roundCoordFactor x * (sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1)))^2 := by
  rw [sourceEuclideanNorm,Real.sq_sqrt (by positivity),Finset.mul_sum]
  unfold Yau.pairing Yau.coordPartial
  apply Finset.sum_congr rfl
  intro i _
  dsimp [roundCoordGradient]
  ring

end
end Yau.Target

end OAI
