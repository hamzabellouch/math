import OAI.Probability.FirstPassage.ProbabilityFoundations

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter
open scoped Topology

def TimeConstantExistenceTarget : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ),
    ExponentialEnvironment P τ → ∃ μ : Plane → ℝ,
      TimeConstantNorm μ ∧ IsTimeConstant P τ μ

def FullMainDifferentiabilityTarget : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ),
    ExponentialEnvironment P τ → ∃ μ : Plane → ℝ,
      TimeConstantNorm μ ∧ IsTimeConstant P τ μ ∧
      DifferentiableAwayFromOrigin μ ∧ UniqueNormalizedSupports μ ∧ C1UnitSphere μ

theorem isTimeConstant_unique {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {τ : Edge → Ω → ℝ} (h : ExponentialEnvironment P τ)
    {μ ν : Plane → ℝ} (hμ : IsTimeConstant P τ μ) (hν : IsTimeConstant P τ ν) : μ=ν := by
  let _ := h.probability
  funext v
  obtain ⟨ω,hω⟩ := ((hμ v).and (hν v)).exists
  exact tendsto_nhds_unique hω.1 hω.2

end PlanarFPP

end OAI
