import OAI.Geometry.PolarProducts.PolarApproximation

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real
open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar
open Set
open scoped ENNReal
noncomputable section
variable {n : ℕ}

theorem gromovWidth_mono {U V : Set (Phase n)} (h : U ⊆ V) :
    gromovWidth U ≤ gromovWidth V := by
  apply sSup_le_sSup
  rintro _ ⟨c, ⟨hc, he⟩, rfl⟩
  exact ⟨c, ⟨hc, he.mono_target h⟩, rfl⟩

theorem four_le_gromovWidth_polarProduct {K : Set (Position n)} (hK : IsSymmetricConvexBody K) :
    4 ≤ gromovWidth (polarProduct K) := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hr4
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  have hr4real : (r : ℝ) < 4 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4)).mp
    simpa using hr4
  apply le_sSup
  refine ⟨(r : ℝ), ⟨hrreal, symmetric_polar_embedding hK hrreal hr4real⟩, ?_⟩
  simp

end
end SymmetricPolar
end LowerBoundInline

end OAI
