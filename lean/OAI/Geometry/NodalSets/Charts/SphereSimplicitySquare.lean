import OAI.Geometry.NodalSets.Charts.SimplicityEnergyDensity
import OAI.Geometry.NodalSets.Charts.SphereDifferentialCoordinates

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

def sphereCrossDifferential (u v : Base → ℝ) (p : Base) : SphereCotangent p :=
  u p • sphereDifferential v p-v p • sphereDifferential u p

lemma roundCotangentTensor_cross_expand (u v : Base → ℝ) (p : Base) :
    roundCotangentTensor p (sphereCrossDifferential u v p) (sphereCrossDifferential u v p) =
      u p^2*roundCotangentTensor p (sphereDifferential v p) (sphereDifferential v p) +
      v p^2*roundCotangentTensor p (sphereDifferential u p) (sphereDifferential u p) -
      2*u p*v p*roundCotangentTensor p (sphereDifferential v p) (sphereDifferential u p) := by
  simp only [sphereCrossDifferential,map_sub,map_smul,sub_apply,
    smul_apply,smul_eq_mul]
  rw [roundCotangentTensor_symm p (sphereDifferential u p) (sphereDifferential v p)]
  ring

lemma sphereCrossDifferential_square_chart (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (p : Base) (x : Yau.Jets.Coord) :
    roundCotangentTensor (sphereChartCoordMap p x)
      (sphereCrossDifferential u v (sphereChartCoordMap p x))
      (sphereCrossDifferential u v (sphereChartCoordMap p x)) =
      roundSimplicitySquare (u ∘ sphereChartCoordMap p) (v ∘ sphereChartCoordMap p) x := by
  rw [roundCotangentTensor_cross_expand,
    roundCotangentTensor_differential_pair v v hv hv,
    roundCotangentTensor_differential_pair u u hu hu,
    roundCotangentTensor_differential_pair v u hv hu]
  unfold roundSimplicitySquare
  simp only [Function.comp_apply,Finset.mul_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma sphereCrossDifferential_square_nonneg (u v : Base → ℝ) (p : Base) :
    0 ≤ roundCotangentTensor p (sphereCrossDifferential u v p) (sphereCrossDifferential u v p) := by
  by_cases h : sphereCrossDifferential u v p = 0
  · simp [h]
  · exact (roundCotangentTensor_pos p _ h).le

end
end Yau.Target

end OAI
