import OAI.MeasureTheory.Falconer.Slicing.GaussianMapBalls
import OAI.MeasureTheory.Falconer.Slicing.SliceCoordinates

namespace OAI

/-! # Coordinate ball estimates for the actual retained slice laws -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem gaussian_pruned_point_kernel_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hs : 2*s+K*((h:ℝ)*(2*δ)) ≤ r i) (a : Space d) :
    (Measure.map (gaussianRowMap A).ker.starProjection
      ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))))
        (ball a s) ≤ TP i := by
  apply gaussian_point_kernel_ball_bound A z _ hK hbound _ (fun x => gaussianPointGood_ball μ δ r TP (A,z) i x) hs a
  exact ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianPointBand_measurable _ _ _)) _)

theorem gaussian_pruned_direction_kernel_ball
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hs : 2*s+4*(K*((h:ℝ)*δ)) ≤ r i) (a : Space d) :
    (Measure.map (fun w : Sphere d => normalize ((gaussianRowMap A).ker.starProjection (w:Space d)))
      ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A)))
        (ball a s) ≤ TD i := by
  apply gaussian_direction_kernel_ball_bound A _ hK hbound hsmall _
    (fun w => gaussianDirectionGood_ball ν δ r TD M A i w) hs a
  exact ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable _ _)) _)

theorem slicePointCoordinates_map_ball (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (μ : Measure (Space d)) (a : Space m) (r : ℝ) :
    (Measure.map (slicePointCoordinates V hm) μ) (ball a r) =
      (Measure.map V.starProjection μ) (ball ((sliceCoordinates V hm).symm a : Space d) r) := by
  rw [Measure.map_apply (slicePointCoordinates_continuous V hm).measurable measurableSet_ball,
    Measure.map_apply V.starProjection.continuous.measurable measurableSet_ball]
  congr 1
  ext x
  change dist (sliceCoordinates V hm (V.orthogonalProjectionOnto x)) a < r ↔ _
  have hd : dist (sliceCoordinates V hm (V.orthogonalProjectionOnto x)) a =
      dist (V.orthogonalProjectionOnto x) ((sliceCoordinates V hm).symm a) := by
    rw [← (sliceCoordinates V hm).dist_map, (sliceCoordinates V hm).apply_symm_apply]
  rw [hd]
  rfl

theorem gaussian_pruned_point_coordinate_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (hm : Module.finrank ℝ (gaussianRowMap A).ker = m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hs : 2*s+K*((h:ℝ)*(2*δ)) ≤ r i) (a : Space m) :
    (Measure.map (slicePointCoordinates (gaussianRowMap A).ker hm)
      ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))))
        (ball a s) ≤ TP i := by
  rw [slicePointCoordinates_map_ball]
  exact gaussian_pruned_point_kernel_ball μ A z δ r TP i hK hbound hs _

theorem sliceDirectionCoordinates_map_ball (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (ν : Measure (Sphere d)) (a : Space m) (r : ℝ) :
    (Measure.map (fun w : Sphere d => normalize (slicePointCoordinates V hm (w:Space d))) ν) (ball a r) =
      (Measure.map (fun w : Sphere d => normalize (V.starProjection (w:Space d))) ν)
        (ball ((sliceCoordinates V hm).symm a : Space d) r) := by
  have hf : Measurable (fun w : Sphere d => slicePointCoordinates V hm (w:Space d)) :=
    (slicePointCoordinates_continuous V hm).measurable.comp measurable_subtype_coe
  have hg : Measurable (fun w : Sphere d => normalize (slicePointCoordinates V hm (w:Space d))) := by
    unfold NormedSpace.normalize
    exact (hf.norm.inv).smul hf
  rw [Measure.map_apply hg measurableSet_ball,
    Measure.map_apply (show Measurable (fun w : Sphere d => normalize (V.starProjection (w:Space d))) from
      by unfold NormedSpace.normalize; fun_prop) measurableSet_ball]
  congr 1
  ext w
  change dist (normalize (sliceCoordinates V hm (V.orthogonalProjectionOnto (w:Space d)))) a < r ↔ _
  rw [← sliceCoordinates_normalize]
  have hd : dist (sliceCoordinates V hm (normalize (V.orthogonalProjectionOnto (w:Space d)))) a =
      dist (normalize (V.orthogonalProjectionOnto (w:Space d))) ((sliceCoordinates V hm).symm a) := by
    rw [← (sliceCoordinates V hm).dist_map,(sliceCoordinates V hm).apply_symm_apply]
  rw [hd]
  rfl

theorem gaussian_pruned_direction_coordinate_ball
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (hm : Module.finrank ℝ (gaussianRowMap A).ker = m)
    (δ : ℝ) (r : ι → ℝ) (TD : ι → ℝ≥0∞) (M : ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hs : 2*s+4*(K*((h:ℝ)*δ)) ≤ r i) (a : Space m) :
    (Measure.map (fun w : Sphere d => normalize (slicePointCoordinates (gaussianRowMap A).ker hm (w:Space d)))
      ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A)))
        (ball a s) ≤ TD i := by
  rw [sliceDirectionCoordinates_map_ball]
  exact gaussian_pruned_direction_kernel_ball ν A δ r TD M i hK hbound hsmall hs _

end Falconer

end OAI
