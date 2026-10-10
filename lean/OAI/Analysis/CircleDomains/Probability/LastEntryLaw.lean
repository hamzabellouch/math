import OAI.Analysis.CircleDomains.Probability.ExitTimeMeasurability
import OAI.Analysis.CircleDomains.Probability.PathHitLaws

namespace OAI

/-! The actual last-entry location law is atomless when the paths avoid
each fixed point of the collar boundary. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def lastEntryLaw (μ : ProbabilityMeasure C(PathTime, X)) (V : Set X) : ProbabilityMeasure X :=
  μ.map (fun γ => γ (lastEntryTime γ V))

theorem lastEntryLaw_singleton_le_hit (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (hV : IsOpen V) (x : X) :
    (lastEntryLaw μ V : Measure X) {x} ≤ pathHitProbability μ x := by
  rw [lastEntryLaw, ProbabilityMeasure.map_apply' μ
    (measurable_lastEntryLocation V hV).aemeasurable (measurableSet_singleton x)]
  apply measure_mono
  intro γ hγ
  exact ⟨lastEntryTime γ V, hγ⟩

omit [SecondCountableTopology X] in
theorem lastEntryLaw_boundary_support (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (hV : IsOpen V)
    (hend : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), γ ⊥ ∉ V ∧ γ ⊤ ∈ V) :
    (lastEntryLaw μ V : Measure X) (frontier V)ᶜ = 0 := by
  rw [lastEntryLaw, ProbabilityMeasure.map_apply' μ
    (measurable_lastEntryLocation V hV).aemeasurable isClosed_frontier.measurableSet.compl]
  apply measure_mono_null (t := {γ | ¬ (γ ⊥ ∉ V ∧ γ ⊤ ∈ V)})
  · intro γ hγ hends
    exact hγ (lastEntry_frontier γ hV hends.1 hends.2)
  · exact ae_iff.mp hend

theorem lastEntryLaw_nullSingletonClass (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (hV : IsOpen V)
    (hend : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), γ ⊥ ∉ V ∧ γ ⊤ ∈ V)
    (havoid : ∀ x ∈ frontier V, pathHitProbability μ x = 0) :
    NullSingletonClass (lastEntryLaw μ V : Measure X) := by
  constructor
  intro x
  by_cases hx : x ∈ frontier V
  · exact le_antisymm ((lastEntryLaw_singleton_le_hit μ V hV x).trans_eq (havoid x hx)) bot_le
  · exact measure_mono_null (singleton_subset_iff.mpr hx)
      (lastEntryLaw_boundary_support μ V hV hend)

end CircleDomainRigidity

end

end OAI
