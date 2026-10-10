import OAI.Geometry.ProjectionBody.SimplexFacetCharts
import OAI.Geometry.ProjectionBody.GraphProjection
import OAI.Geometry.ProjectionBody.SimplexVolume
import OAI.Geometry.ProjectionBody.AffineChartMeasure
import OAI.Geometry.ProjectionBody.BrightnessSum
import OAI.Geometry.ProjectionBody.ProjectionKernel

namespace OAI

noncomputable section
open Set MeasureTheory Measure
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

theorem volume_simplex (n : ℕ) :
    volume (simplex n) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  rw [simplex_eq_coordinates]
  exact volume_unit_euclideanSimplex n

theorem simplexFacetProjection_normDet {n : ℕ} (i : Option (Fin (n + 1)))
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (simplexFacetLinear n i)).normDet =
      |simplexFunctional (n + 1) i u| := by
  cases i with
  | none =>
    change ((project u).toLinearMap.comp
      (graphLinear (Fin.last n) (allOnes n))).normDet = _
    rw [graphProjection_normDet _ _ hu]
    have hnormal : graphNormal (Fin.last n) (allOnes n) = allOnes (n + 1) := by
      ext j
      induction j using Fin.lastCases <;>
        simp [graphNormal, insertZero, Fin.insertNth_last']
    simp [hnormal]
  | some i =>
    change ((project u).toLinearMap.comp (insertZero i).toLinearMap).normDet = _
    rw [coordinateProjection_normDet i hu]
    simp

theorem simplex_projected_facet_volume {n : ℕ} (i : Option (Fin (n + 1)))
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    μHE[n] (project u '' boundingFace (simplexFunctional (n + 1)) simplexLevel i) =
      ENNReal.ofReal ((1 / (n.factorial : ℝ)) * |simplexFunctional (n + 1) i u|) := by
  rw [simplex_facet_eq_affine_image]
  have h := measure_projected_affine_chart (simplexFacetLinear n i)
    (simplexFacetCenter n i) (project u).toLinearMap (simplex n)
  simp only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] at h
  rw [h, simplexFacetProjection_normDet i hu, volume_simplex,
    ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]

theorem simplex_projected_facet_measurable {n : ℕ}
    (i : Option (Fin (n + 1))) (u : E (n + 1)) :
    MeasurableSet (project u '' boundingFace (simplexFunctional (n + 1)) simplexLevel i) := by
  rw [simplex_facet_eq_affine_image]
  apply IsCompact.measurableSet
  apply IsCompact.image _ (project u).continuous
  apply (simplex_compact n).image
  exact continuous_const.add (simplexFacetLinear n i).continuous_of_finiteDimensional

theorem simplex_projected_facet_intersection_null {n : ℕ} (hn : 0 < n)
    (i j : Option (Fin (n + 1))) (hij : i ≠ j) (u : E (n + 1)) :
    μHE[n] (project u ''
      (boundingFace (simplexFunctional (n + 1)) simplexLevel i ∩
        boundingFace (simplexFunctional (n + 1)) simplexLevel j)) = 0 := by
  have hS : boundingFace (simplexFunctional (n + 1)) simplexLevel i ⊆
      (fun x => simplexFacetCenter n i + simplexFacetLinear n i x) '' (univ : Set (E n)) := by
    rw [simplex_facet_eq_affine_image]
    exact Set.image_mono (subset_univ _)
  simpa only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] using
    measure_projected_transverse_intersection (simplexFacetLinear n i)
      (simplexFacetCenter n i) (project u).toLinearMap
      (simplexFunctional (n + 1) j) (simplexLevel j) _ _ hS
      (fun _ h => h.2) (simplex_facet_transverse hn i j hij)

/-- Actual orthogonal projection volume of the convex-hull standard simplex. -/
theorem simplex_projectionVolume {n : ℕ} (hn : 0 < n)
    {u : E (n + 1)} (hu : ‖u‖ = 1) :
    projectionVolume (simplex (n + 1)) u =
      ((∑ i, |u i|) + |∑ i, u i|) / (2 * (n.factorial : ℝ)) := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have h := real_measure_image_halfspaceBody
    (simplexFunctional (n + 1)) simplexLevel (project u).toLinearMap μHE[n]
    (project_self u) (simplex_has_positive_slope hu0) (project_ker u)
    (fun i => simplex_projected_facet_measurable i u)
    (fun i j hij => simplex_projected_facet_intersection_null hn i j hij u)
    (1 / (n.factorial : ℝ)) (by positivity) (simplex_functional_balance u)
    (fun i => simplex_projected_facet_volume i hu)
  rw [← simplex_eq_halfspaceBody, simplex_absolute_slopes] at h
  simp only [ContinuousLinearMap.coe_coe] at h
  unfold projectionVolume
  simp only [Nat.add_sub_cancel]
  rw [h]
  ring

end ProjectionCounterexample

end

end OAI
