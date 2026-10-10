import OAI.Geometry.IsometricImmersion.Coordinates.PatchAddressModel
import OAI.Geometry.IsometricImmersion.Obstructions.SmallPatchObstruction
import OAI.Geometry.IsometricImmersion.Metrics.PatchTensorPositivity

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem exists_obstructing_patch_tensor (a : PatchAddress) :
    ∃ eta : SymmetricPerturbation,
      eta ∈ patchTensorBudgetNeighborhood 1 a ∧
      eta ∈ metricPatchSet (patchAddressInitialMetric a) (patchAddressAmplitude a) ∧
      SmoothPositiveOn (perturbedMetric (patchAddressInitialMetric a) eta) patchAddressModelDomain ∧
      ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric (patchAddressInitialMetric a) eta) z :=
  exists_supported_patch_obstruction_in_open (patchAddressInitialMetric_smoothPositive a)
    patchAddressModelDomain_isOpen modelSquare_subset_patchAddressModelDomain
    (patchAddressAmplitude_pos a) (fun p hp => patchAddressInitialMetric_curvature a hp)
    (patchTensorBudgetNeighborhood_isOpen 1 a)
    (zero_mem_patchTensorBudgetNeighborhood (by norm_num : (0 : ℝ) < 1) a)

def selectedPatchTensor (a : PatchAddress) : SymmetricPerturbation :=
  Classical.choose (exists_obstructing_patch_tensor a)

theorem selectedPatchTensor_spec (a : PatchAddress) :
    selectedPatchTensor a ∈ patchTensorBudgetNeighborhood 1 a ∧
    selectedPatchTensor a ∈ metricPatchSet (patchAddressInitialMetric a) (patchAddressAmplitude a) ∧
    SmoothPositiveOn (perturbedMetric (patchAddressInitialMetric a) (selectedPatchTensor a))
      patchAddressModelDomain ∧
    ∀ z : Coord → ℝ,
      ¬ PatchAdmissibleHeight (perturbedMetric (patchAddressInitialMetric a) (selectedPatchTensor a)) z :=
  Classical.choose_spec (exists_obstructing_patch_tensor a)

theorem selectedPatchTensor_small (a : PatchAddress) :
    selectedPatchTensor a ∈ patchTensorBudgetNeighborhood 1 a :=
  (selectedPatchTensor_spec a).1

theorem selected_local_metric_eq (a : PatchAddress) :
    localPatchMetric initialAssemblyMetric selectedPatchTensor a =
      perturbedMetric (patchAddressInitialMetric a) (selectedPatchTensor a) := rfl

theorem selectedPatchTensor_local_positive (a : PatchAddress) (q : Coord) (hq : q ∈ modelSquare) :
    (localPatchMetric initialAssemblyMetric selectedPatchTensor a q).PosDef := by
  rw [selected_local_metric_eq]
  exact (selectedPatchTensor_spec a).2.1.1 q hq

theorem selectedPatchTensor_local_no_height (a : PatchAddress) :
    ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (localPatchMetric initialAssemblyMetric selectedPatchTensor a) z := by
  rw [selected_local_metric_eq]
  exact (selectedPatchTensor_spec a).2.2.2

end SmoothLocal.Geometry

end

end OAI
