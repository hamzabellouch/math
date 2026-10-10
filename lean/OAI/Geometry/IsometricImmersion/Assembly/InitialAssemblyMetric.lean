import OAI.Geometry.IsometricImmersion.Curvature.InitialCurvature
import OAI.Geometry.IsometricImmersion.Curvature.PrescribedCurvature
import OAI.Geometry.IsometricImmersion.Curvature.AffineCurvature

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.Geometry
open SmoothLocal.ODE SmoothLocal.Model

def initialAssemblyMetric : MetricField := prescribedCurvatureMetric initialCurvature

theorem initialAssemblyMetric_smoothPositiveOn :
    SmoothPositiveOn initialAssemblyMetric square :=
  prescribedCurvatureMetric_smoothPositiveOn initialCurvature_contDiff.contDiffOn
    (fun p _ => initialCurvature_small p)

theorem initialAssemblyMetric_gaussianCurvature {p : Coord} (hp : p ∈ square) :
    gaussianCurvature initialAssemblyMetric p = initialCurvature p :=
  prescribedCurvatureMetric_gaussianCurvature initialCurvature_contDiff.contDiffOn
    (fun p _ => initialCurvature_small p) hp

theorem initialAssemblyMetric_negative_on_disk_interior (n : ℕ) {p : Coord}
    (hp : p ∈ interior (accumulatingDisk n)) : gaussianCurvature initialAssemblyMetric p < 0 := by
  rw [initialAssemblyMetric_gaussianCurvature
    (accumulatingDisk_subset_square n (interior_subset hp))]
  exact initialCurvature_negative_on_disk_interior n hp

theorem initialAssemblyMetric_zero_on_disk_frontier (n : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) : gaussianCurvature initialAssemblyMetric p = 0 := by
  have hdisk : p ∈ accumulatingDisk n := by
    simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using frontier_subset_closure hp
  rw [initialAssemblyMetric_gaussianCurvature (accumulatingDisk_subset_square n hdisk)]
  exact initialCurvature_zero_on_disk_frontier n hp

theorem patch_core_image_mem_square (n k : ℕ) (R : OrientationLabel) (c : Coord)
    (hc : c ∈ orientedExteriorCenters n k R) {q : Coord} (hq : ‖q‖ ≤ 13 / 4) :
    affineCoordinates c (orientedPatchScale n k R • R.val) q ∈ square := by
  apply orientedClosedPatch_subset_square n k R hc
  exact ⟨q, (mem_closedPatchBox_iff_norm_le q).mpr (by linarith), rfl⟩

theorem initialAssemblyMetric_model_in_physical_coordinates (n k : ℕ)
    (R : OrientationLabel) (c : Coord) (hc : c ∈ orientedExteriorCenters n k R)
    {q : Coord} (hq : ‖q‖ ≤ 13 / 4) :
    gaussianCurvature initialAssemblyMetric
      (affineCoordinates c (orientedPatchScale n k R • R.val) q) =
        initialPatchAmplitude n k R c hc * ((q 0) ^ 2 - modelProfile (q 1)) := by
  rw [initialAssemblyMetric_gaussianCurvature (patch_core_image_mem_square n k R c hc hq)]
  exact initialCurvature_model_on_patch n k R c hc hq

theorem initialAssemblyMetric_model_in_patch_coordinates (n k : ℕ)
    (R : OrientationLabel) (c : Coord) (hc : c ∈ orientedExteriorCenters n k R)
    {q : Coord} (hq : ‖q‖ ≤ 13 / 4) :
    gaussianCurvature (affinePullbackMetric initialAssemblyMetric c
      (orientedPatchScale n k R • R.val)) q =
        modelCurvature (initialPatchAmplitude n k R c hc) q := by
  rw [gaussianCurvature_affinePullback initialAssemblyMetric_smoothPositiveOn
    coordinate_square_isOpen c _ (orientedPatchMatrix_isUnit n k R) q
      (patch_core_image_mem_square n k R c hc hq)]
  exact initialAssemblyMetric_model_in_physical_coordinates n k R c hc hq

end SmoothLocal.Geometry

end

end OAI
