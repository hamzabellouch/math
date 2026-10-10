import OAI.Geometry.RCD.Transport.OptimalLengthLaw

namespace OAI

/-! # Restricting length classes commutes with either half subpath -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem length_restriction_subpath
    (π : Measure C(Time,X)) (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (s t : Time) (hst : |(s:ℝ)-(t:ℝ)|=1/2)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (π.restrict {γ | dist (γ 0) (γ 1)∈S}).map (subpath s t)=
      (π.map (subpath s t)).restrict {γ | 2*dist (γ 0) (γ 1)∈S} := by
  have hA : MeasurableSet {γ : C(Time,X) | 2*dist (γ 0) (γ 1)∈S} :=
    hS.preimage (measurable_const.mul ((measurable_path_eval 0).dist (measurable_path_eval 1)))
  rw [Measure.restrict_map (subpath_measurable s t) hA]
  apply congrArg (fun ν : Measure C(Time,X) => ν.map (subpath s t))
  apply Measure.restrict_congr_set
  filter_upwards [hg] with γ hγ
  simp only [mem_ofPred_eq,mem_preimage,subpath_zero,subpath_one,hγ s t,hst]
  congr 1
  ring

end RegularPointCoordinates

end

end OAI
