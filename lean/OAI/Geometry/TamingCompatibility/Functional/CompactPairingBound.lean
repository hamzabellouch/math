import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationChart
import OAI.Geometry.TamingCompatibility.Hodge.HodgeL2Coefficients

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance : NormedAddCommGroup (MetricForms.Form Space 2 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (MetricForms.Form Space 2 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

omit [T2Space X] [CompactSpace X] in
lemma ParametrixData.concentrationCompact_domain {p : X} (D : ParametrixData J α ht p) :
    D.concentrationCompact ⊆ D.chart.domain := by
  rintro y (⟨xy,hxy,rfl⟩ | ⟨xy,hxy,rfl⟩)
  · exact (D.physicalCompact_domain hxy).1
  · exact (D.physicalCompact_domain hxy).2

omit [T2Space X] [CompactSpace X] in
lemma ParametrixData.concentrationPairing_bound {p : X} (D : ParametrixData J α ht p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ D.concentrationCompact,
      ‖MetricForms.pairingCLM (coordinateMetric J α ht p y) 2‖ ≤ C := by
  have hc := MetricForms.pairingCLM_two_smooth (coordinateMetric J α ht p)
    (by simp [Space]) D.chart.frame D.chart.frame_smooth D.chart.frame_gram
  obtain ⟨C,hC⟩ := D.concentrationCompact_compact.exists_bound_of_continuousOn
    (f := fun y => MetricForms.pairingCLM (coordinateMetric J α ht p y) 2)
    (hc.continuousOn.mono D.concentrationCompact_domain)
  exact ⟨max C 0,le_max_right _ _,fun y hy => (hC y hy).trans (le_max_left _ _)⟩

include hE in
omit [T2Space X] [CompactSpace X] in
lemma normalizedFrameEncode_chart_bound (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : TwoForm X) (y : Space), y ∈ (E p).concentrationCompact →
      ‖normalizedFrameEncode A J α ht E ((extChartAt Model p.val).symm y)
        (a ((extChartAt Model p.val).symm y))‖ ≤
          C*‖ManifoldForms.pullback a (extChartAt Model p.val).symm y‖ := by
  obtain ⟨C,hC,hbound⟩ := (E p).concentrationPairing_bound
  refine ⟨Real.sqrt C,Real.sqrt_nonneg _,fun a y hy => ?_⟩
  have he := normalizedFrameEncode_inner A J α ht E hE a a ((extChartAt Model p.val).symm y)
  rw [real_inner_self_eq_norm_sq] at he
  have hp := GeometricAdjoint.pairing_two_chart J α ht p.val a a ((E p).concentrationCompact_target hy)
  rw [← hp] at he
  let v := ManifoldForms.pullback a (extChartAt Model p.val).symm y
  have hb : MetricForms.pairing (coordinateMetric J α ht p.val y) v v ≤ C*‖v‖^2 := by
    calc
      _ ≤ ‖MetricForms.pairingCLM (coordinateMetric J α ht p.val y) 2 v v‖ := le_abs_self _
      _ ≤ ‖MetricForms.pairingCLM (coordinateMetric J α ht p.val y) 2 v‖*‖v‖ :=
        (MetricForms.pairingCLM (coordinateMetric J α ht p.val y) 2 v).le_opNorm v
      _ ≤ (‖MetricForms.pairingCLM (coordinateMetric J α ht p.val y) 2‖*‖v‖)*‖v‖ :=
        mul_le_mul_of_nonneg_right ((MetricForms.pairingCLM (coordinateMetric J α ht p.val y) 2).le_opNorm v) (norm_nonneg _)
      _ ≤ (C*‖v‖)*‖v‖ := by gcongr; exact hbound y hy
      _ = _ := by ring
  have hroot := Real.sq_sqrt hC
  have hp' : 0 ≤ Real.sqrt C*‖v‖ := by positivity
  have he' : (Real.sqrt C*‖v‖)^2 = C*‖v‖^2 := by rw [mul_pow,hroot]
  change _ ≤ Real.sqrt C*‖v‖
  nlinarith [he,hb,norm_nonneg (normalizedFrameEncode A J α ht E ((extChartAt Model p.val).symm y) (a ((extChartAt Model p.val).symm y)))]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
