import Mathlib
import OAI.Analysis.Conductivity.Variational.SymmetricCorrection

namespace OAI

section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology Set TopologicalSpace

theorem dense_weakToStrong_continuityPoints
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [SeparableSpace V] (Z : Set (WeakSpace ℝ V)) (hZ : IsCompact Z) :
    Dense {z : Z | ContinuousAt
      (fun w : Z => (toWeakSpace ℝ V).symm w.val) z} := by
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  apply dense_continuityPoints_of_closed_ball_preimages
  intro y r
  have hclosed : IsClosed ((toWeakSpace ℝ V) '' Metric.closedBall y r) := by
    apply closure_eq_iff_isClosed.mp
    rw [← (convex_closedBall y r).toWeakSpace_closure ℝ,
      Metric.isClosed_closedBall.closure_eq]
  convert hclosed.preimage continuous_subtype_val using 1
  ext z
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro hz
    exact ⟨(toWeakSpace ℝ V).symm z.val, hz, (toWeakSpace ℝ V).apply_symm_apply _⟩
  · rintro ⟨x, hx, heq⟩
    simpa only [← heq, LinearEquiv.symm_apply_apply] using hx

end ScalarConductivity

end
end

end OAI
