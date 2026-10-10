import OAI.Geometry.IsometricImmersion.Assembly.InitialAssemblyMetric
import OAI.Geometry.IsometricImmersion.Assembly.EnumeratedPatchTensors

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation SmoothLocal.Model

def patchAddressInitialMetric (a : PatchAddress) : MetricField :=
  affinePullbackMetric initialAssemblyMetric (patchAddressCenter a) (patchAddressMatrix a)

def patchAddressAmplitude (a : PatchAddress) : ℝ :=
  initialPatchAmplitude a.1 a.2.1 a.2.2.1 a.2.2.2.val a.2.2.2.property

def patchAddressModelDomain : Set Coord := Metric.ball 0 (13/4)

theorem patchAddressAmplitude_pos (a : PatchAddress) : 0 < patchAddressAmplitude a :=
  initialPatchAmplitude_pos a.1 a.2.1 a.2.2.1 a.2.2.2.val a.2.2.2.property

theorem patchAddressModelDomain_isOpen : IsOpen patchAddressModelDomain := Metric.isOpen_ball

theorem modelSquare_subset_patchAddressModelDomain : modelSquare ⊆ patchAddressModelDomain := by
  intro p hp
  have hnorm : ‖p‖ ≤ 3 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using (abs_le.mpr ⟨hp.1 i,hp.2 i⟩)
  change dist p 0 < 13/4
  rw [dist_zero_right]
  linarith

theorem patchAddressModelDomain_mapsTo_square (a : PatchAddress) :
    MapsTo (affineCoordinates (patchAddressCenter a) (patchAddressMatrix a)) patchAddressModelDomain square := by
  intro q hq
  apply patch_core_image_mem_square a.1 a.2.1 a.2.2.1 a.2.2.2.val a.2.2.2.property
  exact (by simpa only [patchAddressModelDomain,Metric.mem_ball,dist_zero_right] using hq : ‖q‖ < 13/4).le

theorem patchAddressInitialMetric_smoothPositive (a : PatchAddress) :
    SmoothPositiveOn (patchAddressInitialMetric a) patchAddressModelDomain := by
  have h := affinePullbackMetric_smoothPositive initialAssemblyMetric_smoothPositiveOn
    (patchAddressCenter a) (patchAddressMatrix a) (Matrix.mulVec_injective_of_isUnit (patchAddressMatrix_isUnit a))
  exact ⟨fun i j => (h.1 i j).mono (patchAddressModelDomain_mapsTo_square a),
    fun p hp => h.2 p (patchAddressModelDomain_mapsTo_square a hp)⟩

theorem patchAddressInitialMetric_curvature (a : PatchAddress) {p : Coord}
    (hp : p ∈ patchAddressModelDomain) :
    gaussianCurvature (patchAddressInitialMetric a) p = modelCurvature (patchAddressAmplitude a) p := by
  apply initialAssemblyMetric_model_in_patch_coordinates a.1 a.2.1 a.2.2.1 a.2.2.2.val a.2.2.2.property
  exact (by simpa only [patchAddressModelDomain,Metric.mem_ball,dist_zero_right] using hp : ‖p‖ < 13/4).le

end SmoothLocal.Geometry

end

end OAI
