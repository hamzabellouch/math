import OAI.Analysis.CircleDomains.Probability.CompactArcLaw

namespace OAI

/-! The boundary start law of compact terminal arcs is atomless whenever
each fixed point of the boundary is missed by the original law. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

def pathStartLaw (η : ProbabilityMeasure C(PathTime, Sphere)) : ProbabilityMeasure Sphere :=
  η.map (fun α => α ⊥)

lemma pathStartLaw_singleton_le_hit (η : ProbabilityMeasure C(PathTime, Sphere)) (x : Sphere) :
    (pathStartLaw η : Measure Sphere) {x} ≤ pathHitProbability η x := by
  rw [pathStartLaw, ProbabilityMeasure.map_apply' η
    (continuous_eval_const ⊥).measurable.aemeasurable (measurableSet_singleton x)]
  exact measure_mono (fun α h => ⟨⊥, h⟩)

lemma pathStartLaw_compl_boundary (η : ProbabilityMeasure C(PathTime, Sphere))
    (V : Set Sphere) (b : Sphere)
    (hη : ∀ᵐ α : C(PathTime, Sphere) ∂(η : Measure C(PathTime, Sphere)),
      α ∈ terminalArcSet V b) :
    (pathStartLaw η : Measure Sphere) (frontier V)ᶜ = 0 := by
  rw [pathStartLaw, ProbabilityMeasure.map_apply' η
    (continuous_eval_const ⊥).measurable.aemeasurable isClosed_frontier.measurableSet.compl]
  apply measure_mono_null (t := {α | α ∉ terminalArcSet V b})
  · intro α h hα
    exact h hα.2.1
  · exact ae_iff.mp hη

theorem pathStartLaw_atomless (μ η : ProbabilityMeasure C(PathTime, Sphere))
    (V : Set Sphere) (b : Sphere)
    (hη : ∀ᵐ α : C(PathTime, Sphere) ∂(η : Measure C(PathTime, Sphere)),
      α ∈ terminalArcSet V b)
    (hhit : ∀ x, pathHitProbability η x ≤ 2 * pathHitProbability μ x)
    (havoid : ∀ x ∈ frontier V, pathHitProbability μ x = 0) :
    NullSingletonClass (pathStartLaw η : Measure Sphere) := by
  constructor
  intro x
  by_cases hx : x ∈ frontier V
  · apply le_antisymm ?_ bot_le
    calc
      (pathStartLaw η : Measure Sphere) {x} ≤ pathHitProbability η x := pathStartLaw_singleton_le_hit η x
      _ ≤ 2 * pathHitProbability μ x := hhit x
      _ = 0 := by rw [havoid x hx, mul_zero]
  · exact measure_mono_null (singleton_subset_iff.mpr hx) (pathStartLaw_compl_boundary η V b hη)

end CircleDomainRigidity

end

end OAI
