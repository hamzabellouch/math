import OAI.Geometry.NodalSets.Charts.SphereChartTransition
import OAI.Geometry.NodalSets.Elliptic.IntrinsicRoundPerturbation
import OAI.Geometry.NodalSets.Elliptic.RoundCoordinateGradient

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

def sphereDifferential (u : Base → ℝ) (p : Base) : SphereCotangent p :=
  mfderiv (𝓡 4) 𝓘(ℝ,ℝ) u p

lemma spherePullback_smooth (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (p : Base) :
    ContDiff ℝ ∞ (u ∘ sphereChartCoordMap p) :=
  (hu.comp (sphereChartCoordMap_smooth p)).contDiff

lemma sphereDifferential_chart_apply (u : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (p : Base) (x w : Yau.Jets.Coord) :
    sphereDifferential u (sphereChartCoordMap p x)
      (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm
        (seedCoordEquiv x) (seedCoordEquiv w)) =
      fderiv ℝ (u ∘ sphereChartCoordMap p) x w := by
  have hi := (inverse_chart_smooth_at (I := 𝓡 4) p (y := seedCoordEquiv x)
    (by rw [centeredSphereChart_target]; trivial)).mdifferentiableAt (by simp)
  have hm := mfderiv_comp x hi seedCoordEquiv.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv,seedCoordEquiv.fderiv] at hm
  have h := mfderiv_comp x (hu.mdifferentiable (by simp) (sphereChartCoordMap p x))
    ((sphereChartCoordMap_smooth p).mdifferentiable (by simp) x)
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ (u ∘ sphereChartCoordMap p) x = _ at h
  change mfderiv 𝓘(ℝ,Yau.Jets.Coord) (𝓡 4) (sphereChartCoordMap p) x = _ at hm
  rw [hm] at h
  exact (congrArg (fun L : Yau.Jets.Coord →L[ℝ] ℝ ↦ L w) h).symm

lemma sphereDifferential_chart (u : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (p : Base) (x : Yau.Jets.Coord) :
    sphereDifferential u (sphereChartCoordMap p x) =
      sphereCoordinateCovector p (seedCoordEquiv x)
        (fun i ↦ Yau.coordPartial (u ∘ sphereChartCoordMap p) x i) := by
  apply sphereCoordinateCovector_unique p (by rw [centeredSphereChart_target]; trivial)
  intro w
  exact (sphereDifferential_chart_apply u hu p x w).trans (coord_covector_sum _ w).symm

lemma roundCotangentTensor_coordinate_pair (p : Base) (x : Yau.Jets.Coord)
    (v w : Fin 4 → ℝ) :
    roundCotangentTensor (sphereChartCoordMap p x)
      (sphereCoordinateCovector p (seedCoordEquiv x) v)
      (sphereCoordinateCovector p (seedCoordEquiv x) w) =
      roundCoordFactor x * ∑ i, v i*w i := by
  change roundCotangentTensor ((extChartAt (𝓡 4) p).symm (seedCoordEquiv x))
    (sphereCoordinateCovector p (seedCoordEquiv x) v)
    (sphereCoordinateCovector p (seedCoordEquiv x) w) = _
  rw [← intrinsicAmbientMatrix_chart_pairing,← intrinsicSphereChartTensor_eq,
    roundCotangentTensor_chart,sphereRoundChartMatrix_inverse_conformal]
  simp only [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct]
  have he : ((4/(‖seedCoordEquiv x‖^2+4))^2)⁻¹ = roundCoordFactor x := by
    unfold roundCoordFactor
    field_simp
  rw [he]
  simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma roundCotangentTensor_differential_pair (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (p : Base) (x : Yau.Jets.Coord) :
    roundCotangentTensor (sphereChartCoordMap p x)
      (sphereDifferential u (sphereChartCoordMap p x))
      (sphereDifferential v (sphereChartCoordMap p x)) =
      roundCoordFactor x * ∑ i, Yau.coordPartial (u ∘ sphereChartCoordMap p) x i *
        Yau.coordPartial (v ∘ sphereChartCoordMap p) x i := by
  rw [sphereDifferential_chart u hu,sphereDifferential_chart v hv,
    roundCotangentTensor_coordinate_pair]

end
end Yau.Target

end OAI
