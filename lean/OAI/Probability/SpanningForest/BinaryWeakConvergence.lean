import OAI.Probability.SpanningForest.CylinderLimitMeasure
import OAI.Probability.SpanningForest.BinaryLawUnique

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336.BinaryLaw

theorem tendsto_iff_signedCylinders
    {I α : Type*} [Countable I] {F : Filter α}
    {μs : α → ProbabilityMeasure (I → Bool)}
    {μ : ProbabilityMeasure (I → Bool)} :
    Tendsto μs F (𝓝 μ) ↔ ∀ A B : Finset I,
      Tendsto (fun a => (μs a : Measure (I → Bool)) (signedCylinder A B)) F
        (𝓝 ((μ : Measure (I → Bool)) (signedCylinder A B))) := by
  constructor
  · intro h A B
    have hv := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h
      (Problem336.isClopen_boolCylinder A B)
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      Function.comp_def, signedCylinder] using (ENNReal.continuous_coe.tendsto _).comp hv
  · intro h
    apply tendsto_nhds_of_unique_mapClusterPt
    intro ν hν
    apply ProbabilityMeasure.toMeasure_injective
    apply measure_ext_of_signed_cylinders
    intro A B
    exact Problem336.clopen_measure_eq_of_mapClusterPt hν
      (Problem336.isClopen_boolCylinder A B) (h A B)

theorem exists_weakLimit_of_signedCylinder_limits
    {I : Type*} [Countable I]
    (μn : ℕ → ProbabilityMeasure (I → Bool))
    (L : Finset I → Finset I → ℝ≥0∞)
    (hL : ∀ A B, Tendsto
      (fun n => (μn n : Measure (I → Bool)) (signedCylinder A B))
      atTop (𝓝 (L A B))) :
    ∃ μ : ProbabilityMeasure (I → Bool),
      (∀ A B, (μ : Measure (I → Bool)) (signedCylinder A B) = L A B) ∧
      Tendsto μn atTop (𝓝 μ) := by
  obtain ⟨μ, hμ⟩ := Problem336.exists_probabilityMeasure_of_boolCylinder_limits μn L hL
  refine ⟨μ, hμ, tendsto_iff_signedCylinders.mpr (fun A B => ?_)⟩
  simpa only [signedCylinder, hμ A B] using hL A B

theorem tendsto_iff_positiveCylinders
    {I α : Type*} [Countable I] {F : Filter α}
    {μs : α → ProbabilityMeasure (I → Bool)}
    {μ : ProbabilityMeasure (I → Bool)} :
    Tendsto μs F (𝓝 μ) ↔ ∀ A : Finset I,
      Tendsto (fun a => (μs a : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}) F
        (𝓝 ((μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true})) := by
  constructor
  · intro h A
    simpa [signedCylinder] using (tendsto_iff_signedCylinders.mp h) A ∅
  · intro h
    apply tendsto_nhds_of_unique_mapClusterPt
    intro ν hν
    apply ProbabilityMeasure.toMeasure_injective
    apply measure_ext_of_positive_cylinders
    intro A
    have hS : IsClopen {x : I → Bool | ∀ i ∈ A, x i = true} := by
      simpa using Problem336.isClopen_boolCylinder A ∅
    exact Problem336.clopen_measure_eq_of_mapClusterPt hν hS (h A)

theorem exists_weakLimit_of_positiveCylinder_limits
    {I : Type*} [Countable I]
    (μn : ℕ → ProbabilityMeasure (I → Bool)) (L : Finset I → ℝ≥0∞)
    (hL : ∀ A, Tendsto
      (fun n => (μn n : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true})
      atTop (𝓝 (L A))) :
    ∃ μ : ProbabilityMeasure (I → Bool),
      (∀ A, (μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true} = L A) ∧
      Tendsto μn atTop (𝓝 μ) := by
  apply Problem336.exists_probabilityMeasure_tendsto_of_clopen_limits μn
    (fun A => {x | ∀ i ∈ A, x i = true}) _ _ L hL
  · intro A
    simpa using Problem336.isClopen_boolCylinder A ∅
  · intro μ ν h
    apply ProbabilityMeasure.toMeasure_injective
    exact measure_ext_of_positive_cylinders h

end Problem336.BinaryLaw

end

end OAI
