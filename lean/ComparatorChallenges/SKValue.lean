import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators

namespace SKValue

noncomputable def standardGaussian : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure standardGaussian := by unfold standardGaussian; infer_instance

noncomputable def gaussianProduct (ι : Type) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι ↦ standardGaussian)
instance gaussianProduct_probability (ι : Type) [Fintype ι] :
    IsProbabilityMeasure (gaussianProduct ι) := by
  unfold gaussianProduct
  infer_instance

def coordinate (N : ℕ) (j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  z ⟨j % (N+1), Nat.mod_lt _ (Nat.succ_pos _)⟩

noncomputable def stepSize (T : ℝ) (N : ℕ) : ℝ := T / N
noncomputable def meshTime (T : ℝ) (N j : ℕ) : ℝ := j * stepSize T N

noncomputable def euler (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (z : Fin (N+1) → ℝ) : ℕ → ℝ
  | 0 => 0
  | j+1 => euler T N γ u z j + Real.sqrt (stepSize T N) * coordinate N j z +
      stepSize T N * γ (meshTime T N j) * u (meshTime T N j) (euler T N γ u z j)

structure OrderParameter where
  coeff : ℝ → ℝ
  nonneg : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ coeff t
  monotone : MonotoneOn coeff (Ico (0 : ℝ) 1)
  rightContinuous : ∀ t ∈ Ico (0 : ℝ) 1, ContinuousWithinAt coeff (Ici t) t
  integrable : IntegrableOn coeff (Ioc (0 : ℝ) 1)

structure BrownianSpace where
  Ω : Type
  measurableSpace : MeasurableSpace Ω
  μ : @Measure Ω measurableSpace
  probability : @IsProbabilityMeasure Ω measurableSpace μ
  B : ℝ≥0 → Ω → ℝ
  measurable : ∀ t, @StronglyMeasurable Ω ℝ _ measurableSpace (B t)
  brownian : @IsBrownianReal Ω measurableSpace B μ

attribute [instance] BrownianSpace.measurableSpace BrownianSpace.probability

noncomputable def BrownianSpace.filtration (W : BrownianSpace) :
    Filtration ℝ≥0 W.measurableSpace := Filtration.natural W.B W.measurable

noncomputable def shiftedFiltration (W : BrownianSpace) (t : ℝ) :
    Filtration ℝ≥0 W.measurableSpace :=
  Filtration.natural (fun s ω ↦ W.B (Real.toNNReal t + s) ω - W.B (Real.toNNReal t) ω)
    (fun _ ↦ (W.measurable _).sub (W.measurable _))

def Admissible (W : BrownianSpace) (t : ℝ) (α : ℝ≥0 → W.Ω → ℝ) : Prop :=
  IsProgressive (shiftedFiltration W t) α ∧ ∀ s ω, |α s ω| ≤ 1

noncomputable def controlPayoff (W : BrownianSpace) (γ : OrderParameter)
    (t x : ℝ) (α : ℝ≥0 → W.Ω → ℝ) : ℝ :=
  ∫ ω, (|x + W.B 1 ω - W.B (Real.toNNReal t) ω +
    ∫ s in (0 : ℝ)..(1-t), γ.coeff (t+s) * α (Real.toNNReal s) ω| -
    (1/2 : ℝ) * ∫ s in (0 : ℝ)..(1-t), γ.coeff (t+s) * α (Real.toNNReal s) ω ^ 2) ∂W.μ

noncomputable def phi (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  sSup {r | ∃ α, Admissible W t α ∧ r = controlPayoff W γ t x α}

noncomputable def gradient (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  deriv (phi W γ t) x

noncomputable def curvature (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  deriv (gradient W γ t) x

noncomputable def parisi (W : BrownianSpace) (γ : OrderParameter) : ℝ :=
  phi W γ 0 0 - (1/2 : ℝ) * ∫ t in (0 : ℝ)..1, t * γ.coeff t

def IsMinimizer (W : BrownianSpace) (γ : OrderParameter) : Prop :=
  ∀ η : OrderParameter, parisi W γ ≤ parisi W η

def IsDiffusion (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ) : Prop :=
  Adapted W.filtration (fun t ω ↦ X (min (t : ℝ) 1) ω) ∧
  (∀ᵐ ω ∂W.μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      X t ω = W.B (Real.toNNReal t) ω +
        ∫ s in (0 : ℝ)..t, γ.coeff s * gradient W γ s (X s ω))

noncomputable def spin (b : Bool) : ℝ := if b then 1 else -1

noncomputable def hamiltonian (n : ℕ) (J : (Fin n × Fin n) → ℝ)
    (σ : Fin n → Bool) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ *
    ∑ i : Fin n, ∑ j : Fin n, if i < j then J (i,j) * spin (σ i) * spin (σ j) else 0

noncomputable def groundStateSequence (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∫ J, sSup (range (hamiltonian n J)) ∂gaussianProduct (Fin n × Fin n)

noncomputable def groundStateValue : ℝ := limUnder atTop groundStateSequence

noncomputable def gradientStopped (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) (U : W.Ω → ℝ) (t : ℝ≥0) (ω : W.Ω) : ℝ :=
  if (t : ℝ) < 1 then gradient W γ t (X t ω) else U ω

def ScalarValueConclusion (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) : Prop :=
  Tendsto groundStateSequence atTop (𝓝 groundStateValue) ∧
  ∃ U : W.Ω → ℝ,
    Martingale (gradientStopped W γ X U) W.filtration W.μ ∧
    (∀ᵐ ω ∂W.μ, |U ω| ≤ 1 ∧ (U ω)^2 = 1 ∧
      Tendsto (fun t ↦ gradient W γ t (X t ω)) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) ∧
    Tendsto (fun t ↦ ∫ ω, (gradient W γ t (X t ω) - U ω)^2 ∂W.μ)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) ∧
    groundStateValue = (∫ ω, |X 1 ω| ∂W.μ) - ∫ t in (0 : ℝ)..1, t * γ.coeff t ∧
    groundStateValue = ∫ ω, U ω * W.B 1 ω ∂W.μ ∧
    groundStateValue = ∫ t in (0 : ℝ)..1, ∫ ω, curvature W γ t (X t ω) ∂W.μ ∧
    IntervalIntegrable (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) volume 0 1

noncomputable def eulerPath (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N : ℕ)
    (z : Fin (N+1) → ℝ) (j : ℕ) : ℝ :=
  euler T N γ.coeff (gradient W γ) z j

noncomputable def rawCoefficient (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  curvature W γ (meshTime T N j) (eulerPath W γ T N z j)

noncomputable def normalizer (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) : ℝ :=
  (Real.sqrt (∫ z, (rawCoefficient W γ T N j z)^2 ∂gaussianProduct (Fin (N+1))))⁻¹

noncomputable def gaussianIncrement (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  normalizer W γ T N j * rawCoefficient W γ T N j z * coordinate N j z

noncomputable def roundedSign (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N : ℕ) (z : Fin (N+1) → ℝ) : ℝ :=
  Real.sign (gradient W γ T (eulerPath W γ T N z N) +
    2 * cdf standardGaussian (coordinate N N z) - 1)

noncomputable def coefficientA (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) : ℝ :=
  if j = 0 then 0 else
    ∫ z, roundedSign W γ T N z * gaussianIncrement W γ T N (j-1) z
      ∂gaussianProduct (Fin (N+1))

noncomputable def coefficientB (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N i : ℕ) : ℝ :=
  ∫ z, roundedSign W γ T N z * coordinate N (i-1) z ∂gaussianProduct (Fin (N+1))

noncomputable def shiftedCoefficientSum (W : BrownianSpace) (γ : OrderParameter)
    (T : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), coefficientA W γ T N j * coefficientB W γ T N (j+1)

def FiniteGaussianConclusion (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) (T : ℝ) : Prop :=
  (∀ᶠ N in atTop, ∀ j < N, 0 < normalizer W γ T N j) ∧
  Tendsto (shiftedCoefficientSum W γ T) atTop
    (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)) ∧
  Tendsto (fun S ↦ ∫ t in (0 : ℝ)..S, ∫ ω, curvature W γ t (X t ω) ∂W.μ)
    (𝓝[<] (1 : ℝ)) (𝓝 groundStateValue)

theorem value_consequences :
    (∀ (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ),
      IsMinimizer W γ → IsDiffusion W γ X → ScalarValueConclusion W γ X) ∧
    (∀ (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ) (T : ℝ),
      0 < T → T < 1 → IsMinimizer W γ → IsDiffusion W γ X →
      FiniteGaussianConclusion W γ X T) ∧
    (∀ (W : BrownianSpace) (γ : OrderParameter),
      IsMinimizer W γ → groundStateValue = parisi W γ) := by
  sorry

end SKValue

end OAI
