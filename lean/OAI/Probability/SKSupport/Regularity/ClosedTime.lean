import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

abbrev ClosedTime := Set.Icc (0 : ℝ) 1

variable {Ω : Type*} [MeasurableSpace Ω]

def closedFiltration (W : BrownianSystem Ω) : Filtration ClosedTime ‹MeasurableSpace Ω› where
  seq t := Filtration.natural W.B (fun s => (W.measurable s).stronglyMeasurable) (Real.toNNReal t)
  mono' := fun _ _ h => (Filtration.natural W.B
    (fun s => (W.measurable s).stronglyMeasurable)).mono (Real.toNNReal_mono h)
  le' t := (Filtration.natural W.B (fun s => (W.measurable s).stronglyMeasurable)).le (Real.toNNReal t)

def terminalGradient (W : BrownianSystem Ω) (γ : OrderParameter)
    (X : ℝ≥0 → Ω → ℝ) (U₁ : Ω → ℝ) (t : ClosedTime) : Ω → ℝ :=
  if (t : ℝ) < 1 then fun ω => gradient W γ t (X (Real.toNNReal t) ω) else U₁

abbrev GaussianSample (N : ℕ) := Fin (N+1) → ℝ

def gaussianLaw (N : ℕ) : Measure (GaussianSample N) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def gaussianCoordinate (N i : ℕ) (z : GaussianSample N) : ℝ :=
  if hi : i < N+1 then z ⟨i, hi⟩ else 0

def meshStep (T : ℝ) (N : ℕ) : ℝ := T / N

def meshTime (T : ℝ) (N j : ℕ) : ℝ := j * meshStep T N

def eulerState (W : BrownianSystem Ω) (γ : OrderParameter) (T : ℝ) (N : ℕ) :
    ℕ → GaussianSample N → ℝ
  | 0, _ => 0
  | j+1, z => eulerState W γ T N j z + Real.sqrt (meshStep T N) * gaussianCoordinate N j z +
      meshStep T N * extend γ.val (meshTime T N j) *
        gradient W γ (meshTime T N j) (eulerState W γ T N j z)

def eulerCurvatureMoment (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) : ℝ :=
  ∫ z, (curvature W γ (meshTime T N (j-1)) (eulerState W γ T N (j-1) z))^2 ∂gaussianLaw N

def eulerNormalizer (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) : ℝ := (Real.sqrt (eulerCurvatureMoment W γ T N j))⁻¹

def normalizedIncrement (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) (z : GaussianSample N) : ℝ :=
  eulerNormalizer W γ T N j *
    curvature W γ (meshTime T N (j-1)) (eulerState W γ T N (j-1) z) *
      gaussianCoordinate N (j-1) z

def randomizedSign (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : ℝ) (N : ℕ) (z : GaussianSample N) : ℝ :=
  (SignType.sign (gradient W γ T (eulerState W γ T N N z) +
    2 * cdf (gaussianReal 0 1) (gaussianCoordinate N N z) - 1) : ℝ)

def gaussianCoeffA (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : ℝ) (N j : ℕ) : ℝ :=
  if j = 0 then 0 else
    ∫ z, randomizedSign W γ T N z * normalizedIncrement W γ T N j z ∂gaussianLaw N

def gaussianCoeffB (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : ℝ) (N i : ℕ) : ℝ :=
  ∫ z, randomizedSign W γ T N z * gaussianCoordinate N (i-1) z ∂gaussianLaw N

def gaussianValueSum (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), gaussianCoeffA W γ T N j * gaussianCoeffB W γ T N (j+1)

end ZeroTemperatureSK

end
end

end OAI
