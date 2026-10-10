import OAI.Geometry.IsometricImmersion.Assembly.SelectedPatchObstructions
import OAI.Geometry.IsometricImmersion.Assembly.AssembledImmersionHeight

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

def counterexampleMetric : MetricField :=
  assembledPatchMetric initialAssemblyMetric selectedPatchTensor

theorem counterexampleMetric_smoothPositive :
    SmoothPositiveOn counterexampleMetric square :=
  assembledPatchMetric_smoothPositive_of_local_metrics (by norm_num : (0 : ℝ) < 1)
    initialAssemblyMetric_smoothPositiveOn selectedPatchTensor selectedPatchTensor_small
    selectedPatchTensor_local_positive

theorem counterexampleMetric_no_local_isometric_immersion
    {U : Set Coord} (hU : IsOpen U) (hUS : U ⊆ square) (h0 : (0 : Coord) ∈ U)
    (F : Coord → Ambient) : ¬ IsometricOn counterexampleMetric F U := by
  intro hF
  obtain ⟨a,_,_,_,_,_,_,_,_,_,hadm⟩ :=
    every_assembled_local_immersion_has_actual_local_height (by norm_num : (0 : ℝ) < 1)
      selectedPatchTensor selectedPatchTensor_small selectedPatchTensor_local_positive hU hUS h0 F hF 0 0
  exact selectedPatchTensor_local_no_height a _ hadm

end SmoothLocal.Geometry

end

end OAI
