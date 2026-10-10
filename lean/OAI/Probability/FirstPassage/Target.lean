import OAI.Probability.FirstPassage.Paths
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def latticeFloor (v : Plane) : Vertex := (⌊v 0⌋, ⌊v 1⌋)

noncomputable def passageTime (τ : Edge → ℝ) (p q : Vertex) : ℝ :=
  sInf {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t}

structure TimeConstantNorm (μ : Plane → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ μ v
  zero_iff : ∀ v, μ v = 0 ↔ v = 0
  triangle : ∀ v w, μ (v + w) ≤ μ v + μ w
  homogeneous : ∀ (a : ℝ) v, μ (a • v) = |a| * μ v

structure ExponentialEnvironment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Edge → Ω → ℝ) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ e, Measurable (τ e)
  independent : iIndepFun τ P
  marginal : ∀ e, Measure.map (τ e) P = expMeasure 1

def IsTimeConstant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Edge → Ω → ℝ) (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, ∀ᵐ ω ∂P,
    Tendsto (fun t : ℝ => passageTime (fun e => τ e ω) (0, 0)
      (latticeFloor (t • v)) / t) atTop (𝓝 (μ v))

def DifferentiableAwayFromOrigin (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, v ≠ 0 → ∃ ℓ : Plane →L[ℝ] ℝ, HasFDerivAt μ ℓ v

def UniqueNormalizedSupports (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, μ v = 1 → ∃! ℓ : Plane →L[ℝ] ℝ,
    ℓ v = 1 ∧ ∀ w, ℓ w ≤ μ w

def C1UnitSphere (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, μ v = 1 → ∃ U : Set Plane, IsOpen U ∧ v ∈ U ∧
    ∃ g : Plane → ℝ, ContDiffOn ℝ 1 g U ∧
      (∀ w ∈ U, μ w = 1 ↔ g w = 0) ∧
      ∀ w ∈ U, g w = 0 → ∃ ℓ : Plane →L[ℝ] ℝ,
        HasFDerivAt g ℓ w ∧ ℓ ≠ 0

def MainDifferentiabilityTarget : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)
    (μ : Plane → ℝ),
    ExponentialEnvironment P τ → TimeConstantNorm μ → IsTimeConstant P τ μ →
      DifferentiableAwayFromOrigin μ ∧ UniqueNormalizedSupports μ ∧ C1UnitSphere μ

end PlanarFPP

end OAI
