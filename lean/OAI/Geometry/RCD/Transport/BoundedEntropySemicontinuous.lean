import OAI.Geometry.RCD.Transport.BoundedEntropyClosed

namespace OAI

/-! # Lower semicontinuity of entropy along a uniformly compressed bounded plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem bounded_entropy_lowerSemicontinuous (μ : Measure X) [SigmaFinite μ]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hs : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ B) :
    LowerSemicontinuous (fun t : Time => boltzmannEntropy μ (π.map (fun γ => γ t))) := by
  let piProb : ProbabilityMeasure C(Time,X) := ⟨π,inferInstance⟩
  let ν := fun y : Time×ℝ => piProb.map (fun γ => γ y.1)
  have hν : Continuous ν := (continuous_time_marginals piProb).comp continuous_fst
  have hclosed := isClosed_compressedKLConstraint (μ.restrict B) hC ν
    (fun y => y.2+(μ.restrict B).real univ-1) hν
    ((continuous_snd.add continuous_const).sub continuous_const)
  apply lowerSemicontinuous_iff_isClosed_epigraph.mpr
  convert hclosed using 1
  ext y
  exact entropy_bound_localized_iff μ (ν y) hB hC (hs y.1) (hc y.1) y.2

end RegularPointCoordinates

end

end OAI
