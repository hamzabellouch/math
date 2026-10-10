import OAI.Geometry.NodalSets.Elliptic.CorrugationCutoff

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

def corrugationFixedCutoff : Coord → ℝ := Classical.choose exists_corrugation_cutoff

lemma corrugationFixedCutoff_spec : ∃ C : ℝ,
    0 < C ∧ ContDiff ℝ ∞ corrugationFixedCutoff ∧ HasCompactSupport corrugationFixedCutoff ∧
    tsupport corrugationFixedCutoff ⊆ ball (0:Coord) (1/2) ∧
    (∀ x, 0 ≤ corrugationFixedCutoff x ∧ corrugationFixedCutoff x ≤ 1) ∧
    (∀ x ∈ closedBall (0:Coord) (1/4), corrugationFixedCutoff =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
    ∀ x, ‖fderiv ℝ corrugationFixedCutoff x‖ ≤ C*(corrugationFixedCutoff x)^((7:ℝ)/8) :=
  Classical.choose_spec exists_corrugation_cutoff

end
end Yau.Geometry

end OAI
