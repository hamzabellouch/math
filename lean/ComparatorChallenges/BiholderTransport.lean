import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)

section MetricDefinitions

variable {M : Type*} [MetricSpace M]

/-- Squared-distance cost with factor one half. -/
def cost (x y : M) : ℝ := dist x y ^ 2 / 2

/-- Calibration of Hausdorff measure to Euclidean volume. -/
def euclideanVolumeFactor (n : ℕ) : ℝ≥0∞ :=
  volume (Metric.ball (0 : Model n) 1) /
    (Measure.hausdorffMeasure (n : ℝ) : Measure (Model n))
      (Metric.ball (0 : Model n) 1)

variable [MeasurableSpace M]

/-- Riemannian volume calibrated to Lebesgue measure in Euclidean space. -/
def metricVolume [BorelSpace M] (n : ℕ) : Measure M :=
  euclideanVolumeFactor n • Measure.hausdorffMeasure (n : ℝ)

/-- Almost-everywhere measurable probability densities between fixed bounds. -/
def AdmissibleDensity (vol : Measure M) (lam cap : ℝ) (rho : M → ℝ) : Prop :=
  AEMeasurable rho vol ∧ Integrable rho vol ∧
  (∫ x, rho x ∂vol) = 1 ∧ (∀ᵐ x ∂vol, lam ≤ rho x ∧ rho x ≤ cap)

/-- Multiplication by a density, ignoring exceptional negative values on null sets. -/
def densityMeasure (vol : Measure M) (rho : M → ℝ) : Measure M :=
  vol.withDensity (fun x => ENNReal.ofReal (rho x))

/-- Optimality for the Monge minimization problem. -/
def IsOptimalMap (vol : Measure M) (rho0 rho1 : M → ℝ) (T : M → M) : Prop :=
  Measurable T ∧ Measure.map T (densityMeasure vol rho0) = densityMeasure vol rho1 ∧
  ∀ S : M → M, Measurable S →
    Measure.map S (densityMeasure vol rho0) = densityMeasure vol rho1 →
    (∫ x, cost x (T x) * rho0 x ∂vol) ≤
      (∫ x, cost x (S x) * rho0 x ∂vol)

/-- The two global estimates have the very same exponent and constant. -/
def BiHolderEstimate (alpha C : ℝ) (T : M ≃ₜ M) : Prop :=
  (∀ x x', dist (T x) (T x') ≤ C * (dist x x') ^ alpha) ∧
  (∀ y y', dist (T.symm y) (T.symm y') ≤ C * (dist y y') ^ alpha)

end MetricDefinitions

section RiemannianDefinitions

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold 𝓘(ℝ, Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]

/-- Complete affinely parametrized geodesic with prescribed initial tangent.
Local metric minimization is an intrinsic definition of Riemannian geodesics. -/
def IsGeodesicWithInitialData (x : M) (v : TangentSpace 𝓘(ℝ, Model n) x)
    (gamma : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n) ∞ gamma ∧
  (⟨gamma 0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n) gamma 0 (1 : ℝ)⟩ :
    TangentBundle 𝓘(ℝ, Model n) M) = ⟨x, v⟩ ∧
  ∀ t : ℝ, ∃ eps : ℝ, 0 < eps ∧
    ∀ s u : ℝ, |s - t| < eps → |u - t| < eps →
      dist (gamma s) (gamma u) = |s - u| * ‖v‖

/-- Evaluation at time one of the geodesic determined by initial data. -/
def riemannianExp (x : M) (v : TangentSpace 𝓘(ℝ, Model n) x) : M := by
  classical
  exact if h : ∃ gamma, IsGeodesicWithInitialData x v gamma then (Classical.choose h) 1 else x

/-- The open injectivity domain, defined by extendible minimizing vectors. -/
def injectivityDomain (x : M) : Set (TangentSpace 𝓘(ℝ, Model n) x) :=
  {p | ∃ a : ℝ, 1 < a ∧ dist x (riemannianExp x (a • p)) = a * ‖p‖}

/-- The Ma–Trudinger–Wang fourth derivative with factor -3/2. -/
def mtw (x : M) (p xi eta : TangentSpace 𝓘(ℝ, Model n) x) : ℝ :=
  -(3 / 2 : ℝ) *
    iteratedDeriv 2 (fun s : ℝ =>
      iteratedDeriv 2 (fun t : ℝ =>
        cost (riemannianExp x (t • xi)) (riemannianExp x (p + s • eta))) 0) 0

/-- Weak MTW only at interior velocities and only for orthogonal test vectors. -/
def WeakMTW : Prop :=
  ∀ (x : M) (p : TangentSpace 𝓘(ℝ, Model n) x), p ∈ injectivityDomain x →
    ∀ xi eta : TangentSpace 𝓘(ℝ, Model n) x,
      inner ℝ xi eta = 0 → 0 ≤ mtw x p xi eta

end RiemannianDefinitions

/-- Uniform bi-Hölder optimal transport for all densities between fixed bounds
on a compact connected smooth Riemannian manifold satisfying weak MTW. -/
theorem uniform_biHolder_transport
    {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ, Model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Model n) ∞ (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]
    [IsRiemannianManifold 𝓘(ℝ, Model n) M]
    [MeasurableSpace M] [BorelSpace M]
    (hmtw : WeakMTW (n := n) (M := M))
    (lam cap : ℝ) (hlam : 0 < lam) (hcap : lam ≤ cap)
    (hclass : ∃ rho : M → ℝ, AdmissibleDensity (metricVolume n) lam cap rho) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 ≤ C ∧
      ∀ rho0 rho1 : M → ℝ,
        AdmissibleDensity (metricVolume n) lam cap rho0 →
        AdmissibleDensity (metricVolume n) lam cap rho1 →
        ∃ T : M ≃ₜ M,
          IsOptimalMap (metricVolume n) rho0 rho1 T ∧
          (∀ S : M → M, IsOptimalMap (metricVolume n) rho0 rho1 S →
            S =ᵐ[densityMeasure (metricVolume n) rho0] T) ∧
          BiHolderEstimate alpha C T := by
  sorry

end WeakMTWTransport

end

end OAI
