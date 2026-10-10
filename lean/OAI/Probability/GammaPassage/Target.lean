import OAI.Probability.GammaPassage.Environment
import OAI.Probability.FirstPassage.Target
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace OAI

namespace GammaFPP
open MeasureTheory
open PlanarFPP

/-- A regular C¹ parametrization of the curve near a point, with a continuous inverse. -/
def HasC1CurveChart (S : Set Plane) (v : Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ v ∈ U ∧ v ∈ S ∧ ∃ γ : ℝ → Plane, ∃ θ : Plane → ℝ,
    ContDiff ℝ 1 γ ∧ ContinuousOn θ U ∧
    (∀ t, γ t ∈ S ∩ U) ∧ (∀ t, θ (γ t)=t) ∧
    (∀ z ∈ S ∩ U, γ (θ z)=z) ∧
    (∀ t, ∃ d : Plane, HasDerivAt γ d t ∧ d ≠ 0)

/-- The Gamma theorem: an actual deterministic passage-time limit norm exists
for every positive shape and rate and every iid environment with that law.
Its Frechet differentiability and literal unit-ball boundary charts are
conclusions. No shape theorem, norm, or no-corner hypothesis is supplied. -/
def GammaDifferentiabilityTarget : Prop :=
  ∀ (shape rate : ℝ), 0 < shape → 0 < rate →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (τ : PlanarFPP.Edge → Ω → ℝ),
      GammaEnvironment shape rate P τ →
        ∃ μ : Plane → ℝ,
          TimeConstantNorm μ ∧ IsTimeConstant P τ μ ∧
          DifferentiableAwayFromOrigin μ ∧
          ∀ v ∈ frontier {z : Plane | μ z ≤ 1},
            HasC1CurveChart (frontier {z : Plane | μ z ≤ 1}) v

end GammaFPP

end OAI
