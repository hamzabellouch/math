import OAI.Analysis.CircleDomains.Topology.CircleQuantileArcs
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

namespace OAI

/-! Transport of atomless boundary laws along an actual circle parametrization. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

theorem circle_supported_map_nullSingletonClass (μ : ProbabilityMeasure X)
    [NullSingletonClass (μ : Measure X)] (c : UnitAddCircle → X)
    (hc : MeasurableEmbedding c) (hs : (μ : Measure X) (range c)ᶜ = 0) :
    NullSingletonClass (μ.map hc.invFun : Measure UnitAddCircle) := by
  constructor
  intro θ
  rw [ProbabilityMeasure.map_apply' μ hc.measurable_invFun.aemeasurable (measurableSet_singleton θ)]
  apply measure_mono_null (t := {c θ} ∪ (range c)ᶜ)
  · intro x hx
    by_cases hr : x ∈ range c
    · left
      obtain ⟨t, rfl⟩ := hr
      have ht : t = θ := (hc.leftInverse_invFun t).symm.trans hx
      exact congrArg c ht
    · exact Or.inr hr
  · exact measure_union_null (measure_singleton (c θ)) hs

theorem ae_circle_coordinate_inverse (μ : ProbabilityMeasure X)
    (c : UnitAddCircle → X) (hc : MeasurableEmbedding c)
    (hs : (μ : Measure X) (range c)ᶜ = 0) :
    ∀ᵐ x ∂(μ : Measure X), c (hc.invFun x) = x := by
  have hr : ∀ᵐ x ∂(μ : Measure X), x ∈ range c := by
    exact ae_iff.mpr hs
  filter_upwards [hr] with x hx
  obtain ⟨θ, rfl⟩ := hx
  rw [hc.leftInverse_invFun θ]

theorem exists_four_circle_arcs_of_supported_law (μ : ProbabilityMeasure X)
    [NullSingletonClass (μ : Measure X)] (c : UnitAddCircle → X)
    (hc : MeasurableEmbedding c) (hs : (μ : Measure X) (range c)ᶜ = 0) :
    ∃ l u : Fin 4 → ℚ,
      (∀ i, 0 < l i ∧ l i < u i ∧ u i < 1 ∧ (1 / 10 : ℝ≥0∞) <
        (μ : Measure X) (hc.invFun ⁻¹' rationalCircleArc (l i) (u i))) ∧
      ∀ i j, i < j → u i < l j := by
  have := circle_supported_map_nullSingletonClass μ c hc hs
  obtain ⟨l, u, hmass, hord⟩ := exists_four_ordered_rational_circle_arcs (μ.map hc.invFun)
  refine ⟨l, u, ?_, hord⟩
  intro i
  refine ⟨(hmass i).1, (hmass i).2.1, (hmass i).2.2.1, ?_⟩
  have h := (hmass i).2.2.2
  rw [ProbabilityMeasure.map_apply' μ hc.measurable_invFun.aemeasurable
    (measurableSet_rationalCircleArc _ _)] at h
  exact h

end CircleDomainRigidity

end

end OAI
