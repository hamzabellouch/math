import OAI.Geometry.RCD.Coordinates.SplittingApproximation
import OAI.Geometry.RCD.Coordinates.RegularTangents

namespace OAI

/-!
# Measured Euclidean approximation and the initial harmonic input

The bounded Lipschitz tests below retain the measure information required
by Huang--Huang Theorem 2.9(1); metric GH closeness alone is not substituted
for it. The convergence input is the noncollapsed volume/measure convergence
of De Philippis--Gigli (2018), Theorems 1.2--1.3.
-/

open Set Metric MeasureTheory Filter
open scoped Topology

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A pointed metric approximation together with the normalized measure
comparison, tested against all bounded 1-Lipschitz functions. -/
structure IsMeasuredEuclideanApproximation (μ : Measure X) (n : ℕ)
    (p : X) (r R ε : ℝ) (f : X → Euclidean n) : Prop where
  metric : IsPointedApproximation p 0 r R ε f
  measurable : Measurable f
  measure_test : ∀ φ : Euclidean n → ℝ, LipschitzWith 1 φ → (∀ z, |φ z| ≤ 1) →
    |(μ.real (ball p (R * r)))⁻¹ * (∫ x in ball p (R * r), φ (f x) ∂μ) -
      (volume.real (ball (0 : Euclidean n) R))⁻¹ *
        (∫ z in ball (0 : Euclidean n) R, φ z)| ≤ ε

/-- The Euclidean-limit specialization of noncollapsed measured volume
convergence, including approximation maps and normalized test integrals. -/
def EuclideanMeasuredRescalingConvergence (μ : Measure X) (n : ℕ) (p : X) : Prop :=
  ∀ r : ℕ → ℝ, (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
    RescalingsConverge p (0 : Euclidean n) r →
    ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ i in atTop,
      ∃ f : X → Euclidean n, IsMeasuredEuclideanApproximation μ n p (r i) R ε f

omit [BorelSpace X] in
/-- All-tangents regularity and the published measured convergence give
a uniform scale threshold for measured, not only metric, approximation. -/
theorem regular_small_scale_measured_approximation {μ : Measure X} {n : ℕ} {p : X}
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular n p)
    (hmeasured : EuclideanMeasuredRescalingConvergence μ n p)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      ∃ f : X → Euclidean n, IsMeasuredEuclideanApproximation μ n p r R ε f := by
  by_contra hnot
  push Not at hnot
  have hchoice (i : ℕ) : ∃ r : ℝ, 0 < r ∧ r < 1 / ((i : ℝ) + 1) ∧
      ∀ f : X → Euclidean n, ¬IsMeasuredEuclideanApproximation μ n p r R ε f :=
    hnot (1 / ((i : ℝ) + 1)) (by positivity)
  choose r hrpos hrsmall hrbad using hchoice
  have hrzero : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun i => (hrpos i).le) (fun i => (hrsmall i).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv := regular_rescalings_converge hcompact hregular r hrpos hrzero
  obtain ⟨i, f, hf⟩ := (hmeasured r hrpos hrzero hconv R ε hR hε).exists
  exact hrbad i f hf

/-- Huang--Huang Theorem 2.9(1), specialized to the Euclidean target.
The enlarged measured ball leaves room for a compact Sobolev extension
of the local harmonic map without changing it on the output ball. -/
def LocalInitialSplittingInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∀ β : ℝ, 0 < β → ∃ ε : ℝ, 0 < ε ∧
    ∀ (p : X) (r : ℝ), 0 < r → -ε ≤ K * r ^ 2 →
      (∃ f : X → Euclidean n,
        IsMeasuredEuclideanApproximation (hausdorff n X) n p r 16 ε f) →
      ∃ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2 * r) β u v

end RegularPointCoordinates

end

end OAI
