import OAI.Probability.MemoryPrecision.KernelModel
import OAI.Probability.MemoryPrecision.AmbientGram
import OAI.Probability.MemoryPrecision.SharpGaussian
import OAI.Probability.MemoryPrecision.DensityPassage
import OAI.Probability.MemoryPrecision.FiniteDensity
import OAI.Probability.MemoryPrecision.MeasurableTests
import OAI.Probability.MemoryPrecision.WeightedSelection
import OAI.Probability.MemoryPrecision.WeightedImage
import OAI.Probability.MemoryPrecision.CoefficientStep
import OAI.Probability.MemoryPrecision.RealContinuation
import OAI.Probability.MemoryPrecision.StochasticContinuation
import OAI.Probability.MemoryPrecision.KernelEvaluation
import OAI.Probability.MemoryPrecision.KernelIntegral
import OAI.Probability.MemoryPrecision.SphereCaps
import OAI.Probability.MemoryPrecision.CubeGeometry
import OAI.Probability.MemoryPrecision.CubeBlock
import OAI.Probability.MemoryPrecision.CubeCaps
import OAI.Probability.MemoryPrecision.CubeContinuation
import OAI.Probability.MemoryPrecision.StochasticMass
import OAI.Probability.MemoryPrecision.PriorMeasurability
import OAI.Probability.MemoryPrecision.CubeExperiment
import OAI.Probability.MemoryPrecision.KernelCaps
import OAI.Probability.MemoryPrecision.KernelVersion
import OAI.Probability.MemoryPrecision.SeedAverage
import OAI.Probability.MemoryPrecision.KernelSphere
import OAI.Probability.MemoryPrecision.KernelAdmissibility
import OAI.Probability.MemoryPrecision.CubeArithmetic
import OAI.Probability.MemoryPrecision.KernelCube
import OAI.Probability.MemoryPrecision.RealStream
import OAI.Probability.MemoryPrecision.ZeroHorizon
import OAI.Probability.MemoryPrecision.SuccessArithmetic
import OAI.Probability.MemoryPrecision.EllipsoidSuccess
import OAI.Probability.MemoryPrecision.StreamArithmetic
import OAI.Probability.MemoryPrecision.KernelEllipsoid
import OAI.Probability.MemoryPrecision.StreamZero
import OAI.Probability.MemoryPrecision.KernelStream
import OAI.Probability.MemoryPrecision.Reflection
import OAI.Probability.MemoryPrecision.Precision
import OAI.Probability.MemoryPrecision.CubeSuccess
import OAI.Probability.MemoryPrecision.LabelTranslations
import OAI.Probability.MemoryPrecision.JointL1
import OAI.Probability.MemoryPrecision.SphericalProjection
import OAI.Probability.MemoryPrecision.PointwiseDensity
import OAI.Probability.MemoryPrecision.RadialMixture
import OAI.Probability.MemoryPrecision.BallAverages
import OAI.Probability.MemoryPrecision.GaussianConvolution
import OAI.Probability.MemoryPrecision.FiberDensity
import OAI.Probability.MemoryPrecision.DensityUniqueness
import OAI.Probability.MemoryPrecision.PointwiseMain

namespace OAI

universe u
namespace MemoryPrecision

open MeasureTheory
open scoped ENNReal

theorem main :
  AmbientGramStatement ∧
  FiniteDensityStatement ∧
  MeasurableTestStatement ∧
  JointL1Statement ∧
  PointwiseDensityStatement ∧
  CoefficientStepStatement ∧
  Kernel.SourceEllipsoidStatement.{u} ∧
  CubeBlockStatement ∧
  (∃ D : ℝ, Real.exp 1 ≤ D ∧ ∃ d₀ : ℕ, ∃ hd₀ : 16 ≤ d₀, ∃ c : ℝ, 0 < c ∧
    ∀ d M T : ℕ, ∀ hd : d₀ ≤ d, M ≤ d^2 → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ K : Ω → MemoryPrecision.Kernel.Policy d M T,
      MemoryPrecision.Kernel.Policy.ModelAdmissible.{u} K ρ →
      MemoryPrecision.Kernel.Policy.Success K ρ
        (MemoryPrecision.Kernel.CubePrior (MemoryPrecision.Kernel.cubePrior_dimension hd₀ hd)) ε ≤
          min 1 (ENNReal.ofReal
            (D^((d/2)*(MemoryPrecision.Kernel.BlockCount T ((d/2)/4)+1)) * ε^((d/2:ℕ)/4:ℝ))) ∧
      ((∀ signal : MemoryPrecision.Kernel.Sphere d,
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) /
        (@OfNat.ofNat ℝ≥0∞ 3
          (@instOfNatAtLeastTwo ℝ≥0∞ 3 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) ≤
          (∫⁻ observation,
            MemoryPrecision.Kernel.Policy.experiment K
              (MemoryPrecision.Kernel.Policy.angleTest ε) (signal, observation)
            ∂ρ.prod (MemoryPrecision.Kernel.RowLaw d T))) →
        c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ))) ∧
  (∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 0 < d₀ ∧
    ∀ d M T : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → MemoryPrecision.Kernel.Policy d M T,
      MemoryPrecision.Kernel.Policy.Admissible L ρ (MemoryPrecision.Kernel.UniformSphere d) →
      MemoryPrecision.Kernel.Policy.Success L ρ (MemoryPrecision.Kernel.UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
        ((2*ε*Real.exp (C*(1+(M:ℝ)/(d:ℝ)^2)*(MemoryPrecision.Kernel.BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2)))) :=
  ⟨ambient_gram, finite_density, measurable_test, joint_l1, pointwise_density, coefficient_step, Kernel.source_ellipsoid_success, cube_block, Kernel.source_cube_success, Kernel.source_stream_success⟩

end MemoryPrecision

end OAI
