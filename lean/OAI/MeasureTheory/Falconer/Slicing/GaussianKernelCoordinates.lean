import OAI.MeasureTheory.Falconer.Slicing.GaussianKernelGeometry
import OAI.MeasureTheory.Falconer.Slicing.SliceBallTransfer

namespace OAI

/-! # Metric control in the kernel coordinates of a Gaussian slice -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d h : ℕ}

theorem gaussian_point_kernel_pair_distance (A : Fin h → Space d) (z : Space h)
    {K r s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r)
    (hxy : ‖(gaussianRowMap A).ker.starProjection x-
      (gaussianRowMap A).ker.starProjection y‖ ≤ s) :
    ‖x-y‖ ≤ s+K*((h:ℝ)*(2*r)) := by
  have he : x-y = (gaussianRowMap A).ker.starProjection (x-y)+
      (gaussianRowMap A).kerᗮ.starProjection (x-y) := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  calc
    _ ≤ ‖(gaussianRowMap A).ker.starProjection (x-y)‖+
        ‖(gaussianRowMap A).kerᗮ.starProjection (x-y)‖ := by
      conv_lhs => rw [he]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add (by simpa only [map_sub] using hxy)
      (gaussian_point_band_kernel_difference A z hK hbound hx hy)

theorem gaussian_direction_kernel_normalize_error (A : Fin h → Space d)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hr : K*((h:ℝ)*r) < 1) {w : Sphere d} (hw : w ∈ gaussianDirectionBand A r) :
    ‖normalize ((gaussianRowMap A).ker.starProjection (w:Space d))-(w:Space d)‖ ≤
      2*(K*((h:ℝ)*r)) :=
  directionSliceBand_normalize_error _ hr (gaussian_direction_band_kernel_distance A hK hbound hw)

theorem gaussian_direction_kernel_nonzero (A : Fin h → Space d)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hr : K*((h:ℝ)*r) < 1) {w : Sphere d} (hw : w ∈ gaussianDirectionBand A r) :
    (gaussianRowMap A).ker.starProjection (w:Space d) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (sub_pos.mpr hr).trans_le (directionSliceBand_projection_lower _
    (gaussian_direction_band_kernel_distance A hK hbound hw))

end Falconer

end OAI
