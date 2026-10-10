import OAI.Geometry.ProjectionBody.ProductFacetProjection
import OAI.Geometry.ProjectionBody.SimplexBrightness
import OAI.Geometry.ProjectionBody.ProductVolumes

namespace OAI

noncomputable section
open Set MeasureTheory Measure

namespace ProjectionCounterexample

theorem product_projected_facet_volume (i : Bool × Option (Fin 10))
    {u : E 20} (hu : ‖u‖ = 1) :
    μHE[19] (project u '' boundingFace productFunctional productLevel i) =
      ENNReal.ofReal ((1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) *
        |productFunctional i u|) := by
  rw [product_facet_eq_affine_image]
  have h := measure_projected_affine_chart (productFacetLinear i)
    (productFacetCenter i) (project u).toLinearMap (productFacetDomain i.1)
  simp only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] at h
  rw [h, productFacetProjection_normDet i hu, volume_productFacetDomain,
    ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]

theorem product_projected_facet_measurable
    (i : Bool × Option (Fin 10)) (u : E 20) :
    MeasurableSet (project u '' boundingFace productFunctional productLevel i) := by
  rw [product_facet_eq_affine_image]
  apply IsCompact.measurableSet
  apply IsCompact.image _ (project u).continuous
  apply (productFacetDomain_compact i.1).image
  exact continuous_const.add (productFacetLinear i).continuous_of_finiteDimensional

theorem product_projected_facet_intersection_null
    (i j : Bool × Option (Fin 10)) (hij : i ≠ j) (u : E 20) :
    μHE[19] (project u ''
      (boundingFace productFunctional productLevel i ∩
        boundingFace productFunctional productLevel j)) = 0 := by
  have hS : boundingFace productFunctional productLevel i ⊆
      (fun x => productFacetCenter i + productFacetLinear i x) '' (univ : Set (E 19)) := by
    rw [product_facet_eq_affine_image]
    exact Set.image_mono (subset_univ _)
  simpa only [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] using
    measure_projected_transverse_intersection (productFacetLinear i)
      (productFacetCenter i) (project u).toLinearMap (productFunctional j) (productLevel j)
      _ _ hS (fun _ h => h.2) (product_facet_transverse i j hij)

/-- Actual orthogonal projection volume of the twenty-dimensional product body. -/
theorem product_projectionVolume {u : E 20} (hu : ‖u‖ = 1) :
    projectionVolume productBody u =
      (((∑ i, |firstBlock u i|) + |∑ i, firstBlock u i|) +
        ((∑ i, |secondBlock u i|) + |∑ i, secondBlock u i|)) /
      (2 * ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have h := real_measure_image_halfspaceBody
    productFunctional productLevel (project u).toLinearMap μHE[19]
    (project_self u) (product_has_positive_slope hu0) (project_ker u)
    (fun i => product_projected_facet_measurable i u)
    (fun i j hij => product_projected_facet_intersection_null i j hij u)
    (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) (by positivity)
    (product_functional_balance u) (fun i => product_projected_facet_volume i hu)
  rw [← productBody_eq_halfspaceBody, product_absolute_slopes] at h
  simp only [ContinuousLinearMap.coe_coe] at h
  unfold projectionVolume
  change (μHE[19] (project u '' productBody)).toReal = _
  rw [h]
  ring

end ProjectionCounterexample

end

end OAI
