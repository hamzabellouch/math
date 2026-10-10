import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.PlaneTransverseGraph

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory RadialPotential PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def unitTransverseCut (p : X) (b : Space) (K : Set Space) :
    MetricUnit (hermitianMetric J α hs ht) → Space :=
  (unitChartDomain J α hs ht p K).indicator (unitTransverse J α hs ht p b)

def unitDistanceCut (p : X) (b : Space) (K : Set Space) :
    MetricUnit (hermitianMetric J α hs ht) → ℝ :=
  (unitChartDomain J α hs ht p K).indicator (fun u => ‖unitChartBase J α hs ht p u-b‖)

omit [CompactSpace X] in
lemma unitTransverseCut_measurable (p : X) (b : Space) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) : Measurable (unitTransverseCut J α hs ht p b K) := by
  classical
  exact (unitTransverse_continuousOn J α hs ht p b hKT).measurable_piecewise continuousOn_const
    (unitChartDomain_closed J α hs ht p hK hKT).measurableSet

omit [CompactSpace X] in
lemma unitDistanceCut_measurable (p : X) (b : Space) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) : Measurable (unitDistanceCut J α hs ht p b K) := by
  classical
  exact ((unitChartBase_continuousOn J α hs ht p hKT).sub continuousOn_const).norm.measurable_piecewise
    continuousOn_const (unitChartDomain_closed J α hs ht p hK hKT).measurableSet

omit [CompactSpace X] [T2Space X] in
lemma unitTransverseCut_zero (p : X) (b : Space) (K : Set Space)
    (u : MetricUnit (hermitianMetric J α hs ht)) (hu : unitDistanceCut J α hs ht p b K u = 0) :
    unitTransverseCut J α hs ht p b K u = 0 := by
  by_cases h : u ∈ unitChartDomain J α hs ht p K
  · rw [unitDistanceCut,indicator_of_mem h,norm_eq_zero] at hu
    simp only [unitTransverseCut,indicator_of_mem h,unitTransverse,hu,transverse,inner_zero_right,
      zero_smul,sub_zero]
  · exact indicator_of_notMem h _
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
