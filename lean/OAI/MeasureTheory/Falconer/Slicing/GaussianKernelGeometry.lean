import OAI.MeasureTheory.Falconer.Slicing.GaussianRowMap
import OAI.MeasureTheory.Falconer.Slicing.SliceGeometry

namespace OAI

/-! # Passing from Gaussian row bands to their actual kernel planes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem linearMap_orthogonal_kernel_projection (L : Space d →L[ℝ] Space h) (x : Space d) :
    L (L.kerᗮ.starProjection x) = L x := by
  rw [Submodule.starProjection_orthogonal_val,map_sub]
  have hz : L (L.ker.starProjection x) = 0 := (L.ker.orthogonalProjectionOnto x).property
  rw [hz,sub_zero]

theorem linearMap_kernel_projection_bound (L : Space d →L[ℝ] Space h) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Space d, ‖L.kerᗮ.starProjection x‖ ≤ K*‖L x‖ := by
  let F : L.kerᗮ →L[ℝ] Space h := L.comp L.kerᗮ.subtypeL
  have hf : LinearMap.ker F.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hmem : (x:Space d) ∈ L.ker := hx
    have hz : (x:Space d) = 0 := inner_self_eq_zero.mp
      (L.ker.inner_right_of_mem_orthogonal hmem x.property)
    exact Subtype.ext hz
  obtain ⟨K,hK,hLip⟩ := F.toLinearMap.exists_antilipschitzWith hf
  refine ⟨K,by exact_mod_cast hK,?_⟩
  intro x
  have hh := (antilipschitzWith_iff_le_mul_dist.mp hLip) (L.kerᗮ.orthogonalProjectionOnto x) 0
  change dist (L.kerᗮ.orthogonalProjectionOnto x) 0 ≤
    (K:ℝ)*dist (L (L.kerᗮ.starProjection x)) (L 0) at hh
  simp only [dist_zero_right,map_zero] at hh
  change ‖L.kerᗮ.starProjection x‖ ≤ (K:ℝ)*‖L (L.kerᗮ.starProjection x)‖ at hh
  rwa [linearMap_orthogonal_kernel_projection] at hh

theorem gaussian_direction_band_kernel_distance (A : Fin h → Space d)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {w : Sphere d} (hw : w ∈ gaussianDirectionBand A r) :
    ‖(gaussianRowMap A).kerᗮ.starProjection (w:Space d)‖ ≤ K*((h:ℝ)*r) := by
  exact (hbound w).trans (mul_le_mul_of_nonneg_left (gaussianRowMap_norm_le_of_bands A w hw) hK)

theorem gaussian_point_band_kernel_difference (A : Fin h → Space d) (z : Space h)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r) :
    ‖(gaussianRowMap A).kerᗮ.starProjection (x-y)‖ ≤ K*((h:ℝ)*(2*r)) :=
  (hbound (x-y)).trans (mul_le_mul_of_nonneg_left
    (gaussianRowMap_norm_le_of_bands A (x-y) (gaussianPointBand_pair_difference A z hx hy)) hK)

end Falconer

end OAI
