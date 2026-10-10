import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.FiniteCharts

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldLocalization
open Set ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X)
attribute [local instance] Classical.propDecidable

def coordinatePartition (p : A.centers) : Space → ℝ :=
  (extChartAt Model p.val).target.indicator (fun q => A.partition p ((extChartAt Model p.val).symm q))

omit [T2Space X] in
lemma coordinatePartition_smooth_compact (p : A.centers) :
    ContDiff ℝ ∞ (coordinatePartition A p) ∧ HasCompactSupport (coordinatePartition A p) := by
  apply smooth_indicator_of_compact (isOpen_extChartAt_target p.val)
    (coordinateSupport_compact A p) (coordinateSupport_subset A p)
  · exact (A.partition p).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm p.val) |>.contDiffOn
  · intro q hq hK
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    exact hK ⟨(extChartAt Model p.val).symm q,hh,(extChartAt Model p.val).right_inv hq⟩

omit [T2Space X] [CompactSpace X] in
lemma coordinatePartition_support (p : A.centers) :
    Function.support (coordinatePartition A p) ⊆ coordinateSupport A p := by
  intro q hq
  have ht : q ∈ (extChartAt Model p.val).target := by
    by_contra h
    exact hq (Set.indicator_of_notMem h _)
  refine ⟨(extChartAt Model p.val).symm q,subset_tsupport _ ?_,(extChartAt Model p.val).right_inv ht⟩
  change _ ≠ 0
  change coordinatePartition A p q ≠ 0 at hq
  simpa only [coordinatePartition,Set.indicator_of_mem ht] using hq

omit [T2Space X] in
lemma coordinatePartition_tsupport (p : A.centers) :
    tsupport (coordinatePartition A p) ⊆ coordinateSupport A p :=
  closure_minimal (coordinatePartition_support A p) (coordinateSupport_compact A p).isClosed

omit [T2Space X] [CompactSpace X] in
lemma coordinatePartition_bounds (p : A.centers) (q : Space) :
    0 ≤ coordinatePartition A p q ∧ coordinatePartition A p q ≤ 1 := by
  by_cases hq : q ∈ (extChartAt Model p.val).target
  · simp only [coordinatePartition,Set.indicator_of_mem hq]
    exact ⟨A.partition.nonneg _ _,A.partition.le_one _ _⟩
  · simp only [coordinatePartition,Set.indicator_of_notMem hq,le_refl,zero_le_one,and_self]

omit [T2Space X] [CompactSpace X] in
lemma coordinatePartition_apply (p : A.centers) {x : X}
    (hx : x ∈ (extChartAt Model p.val).source) :
    coordinatePartition A p (extChartAt Model p.val x) = A.partition p x := by
  simp only [coordinatePartition,Set.indicator_of_mem ((extChartAt Model p.val).map_source hx),
    (extChartAt Model p.val).left_inv hx]

end TamingCompatibility.ManifoldLocalization

end
end

end

end OAI
