import OAI.Analysis.IrrationalRotation.Model.ScalarKernelEstimates
import OAI.Analysis.IrrationalRotation.Model.UniformIntervalPhase
import Mathlib.Analysis.Complex.Basic

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

def samplingHorizon (m : ℕ) : ℝ := (m : ℝ) ^ ((7 / 10 : ℝ) * m)

def bvSize (f : ℝ → ℂ) : ℝ :=
  sSup ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1) +
    (eVariationOn f (Icc (0 : ℝ) 1)).toReal

def SeparatedPowers (m : ℕ) (N : ℝ) (n n' : ℕ) : Prop :=
  ∀ v v' : ℤ, |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
    (v ≠ 0 ∨ v' ≠ 0) →
      N * (m : ℝ) ^ 1000 < |(v : ℝ) * n + (v' : ℝ) * n'|

structure SamplingPair (m : ℕ) (N₀ N : ℝ) (n n' : ℕ) : Prop where
  N₀_pos : 0 < N₀
  N₀_le : N₀ ≤ N
  N_le : N ≤ (m : ℝ)^2
  n_pos : 0 < n
  n'_pos : 0 < n'
  distinct : n ≠ n'
  first_range : samplingHorizon m / 2 ≤ n ∧ (n : ℝ) ≤ samplingHorizon m
  second_range : samplingHorizon m / 2 ≤ n' ∧ (n' : ℝ) ≤ samplingHorizon m
  separated : SeparatedPowers m N n n'

def rectangleProbability (N₀ : ℝ) (n n' : ℕ) (a b c d : ℝ) : ℝ :=
  (UniformIntervalPhase.lambdaLaw N₀).real
    {x | Int.fract ((n : ℝ) * x) ∈ Ico a b ∧
      Int.fract ((n' : ℝ) * x) ∈ Ico c d}

def RectangleEstimate (m : ℕ) (N₀ : ℝ) (n n' : ℕ) (C : ℝ) : Prop :=
  ∀ a b c d : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    0 ≤ c → c ≤ d → d ≤ 1 →
      |rectangleProbability N₀ n n' a b c d - (b - a) * (d - c)| ≤
        C * (m : ℝ)^(-(80 : ℝ))

def BVEstimate (m : ℕ) (N₀ : ℝ) (n n' : ℕ) (C : ℝ) : Prop :=
  ∀ f g : ℝ → ℂ,
    BoundedVariationOn f (Icc (0 : ℝ) 1) →
    BoundedVariationOn g (Icc (0 : ℝ) 1) →
      ‖(∫ x, f (Int.fract ((n : ℝ) * x)) * g (Int.fract ((n' : ℝ) * x))
          ∂UniformIntervalPhase.lambdaLaw N₀) -
        (∫ x in (0 : ℝ)..1, f x) * (∫ x in (0 : ℝ)..1, g x)‖ ≤
          C * (m : ℝ)^(-(80 : ℝ)) * bvSize f * bvSize g

def AllKernelEstimates : Prop :=
  ∀ m : ℕ, 200 ≤ m →
    KernelEstimates m (manuscriptKernel m) ∧
      KernelEstimates m (manuscriptEndpointKernel m)

def AllMarginalEstimates : Prop :=
  ∀ N₀ n : ℝ, 0 < N₀ → 0 < n →
    Measurable (UniformIntervalPhase.fractionDensity N₀ n) ∧
      (∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1),
        0 ≤ UniformIntervalPhase.fractionDensity N₀ n x ∧
          |UniformIntervalPhase.fractionDensity N₀ n x - 1| ≤ N₀ / n) ∧
      (volume.restrict (Ico (0 : ℝ) 1)).withDensity
        (fun x => ENNReal.ofReal (UniformIntervalPhase.fractionDensity N₀ n x)) =
          UniformIntervalPhase.fractionLaw N₀ n

def AllSeparatedEstimates : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ, 200 ≤ M ∧
    ∀ m : ℕ, M ≤ m → ∀ N₀ N : ℝ, ∀ n n' : ℕ,
      SamplingPair m N₀ N n n' →
        RectangleEstimate m N₀ n n' C ∧ BVEstimate m N₀ n n' C

structure ScalarSamplingEstimates : Prop where
  kernel : AllKernelEstimates
  marginal : AllMarginalEstimates
  separated : AllSeparatedEstimates

end Invariant233.ScalarSampling

end

end OAI
