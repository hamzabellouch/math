import OAI.Geometry.RCD.Sobolev.DimensionalBochnerTest
import OAI.Geometry.RCD.Coordinates.RegularCoreBochner

namespace OAI

/-! # The scalar finite-dimensional Bochner inequality and its measure form

Han, JGA 28 (2018), Theorem 3.3, gives the scalar Bakry--Émery inequality
on compact Lipschitz functions with L² Laplacian. The finite-family measure
identities use the full positive regular Bochner measure.
-/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The scalar weak BE(K,N) inequality on the compact regular class used
in this application. The mixed source is interpreted by the actual
weak Laplacian; no Sobolev derivative of that source is required. -/
def ScalarDimensionalBochner (K N : ℝ) : Prop :=
  ∀ (u : SobolevSpace μ hQ) (v : X → ℝ) (L : ℝ≥0),
    LipschitzWith L v → HasCompactSupport v →
    SobolevSpace.toLp μ hQ u =ᵐ[μ] v →
    ∀ (d : Lp ℝ 2 μ), IsWeakLaplacian μ hQ u d →
    ∀ (G : SobolevSpace μ hQ),
      SobolevSpace.toLp μ hQ G =ᵐ[μ] localGamma μ hQ u u →
    ∀ (q : X →ᵇ ℝ) (ψ : SobolevSpace μ hQ) (A : ℝ≥0),
      LipschitzWith A q → HasCompactSupport (q : X → ℝ) →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q → 0≤q →
      (∫ x, q x*(d x)^2 ∂μ) ≤ N*(bochnerTestForm μ hQ (-K) G ψ+
        weightedLaplacianPair μ q d d+weightedGamma μ hQ d u ψ)

/-- The scalar test formula is exactly the diagonal of the existing
bilinear Bochner form, including its L² source terms. -/
theorem ScalarDimensionalBochner.regular_form {K N : ℝ}
    (h : ScalarDimensionalBochner μ hQ K N) {m : ℕ}
    (U : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    (hc : ∀ a, ∃ (v : X → ℝ) (A : ℝ≥0), LipschitzWith A v ∧
      HasCompactSupport v ∧ SobolevSpace.toLp μ hQ (U a) =ᵐ[μ] v)
    (hD : ∀ a, IsWeakLaplacian μ hQ (U a) (D a))
    (hH : ∀ a, SobolevSpace.toLp μ hQ (H a a) =ᵐ[μ] localGamma μ hQ (U a) (U a))
    (a : Euclidean m) (q : X →ᵇ ℝ) (ψ : SobolevSpace μ hQ) (A : ℝ≥0)
    (hq : LipschitzWith A q) (hqc : HasCompactSupport (q : X → ℝ))
    (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q) (hq0 : 0≤q) :
    (∫ x, q x*(D a x)^2 ∂μ)≤N*regularBochnerForm μ hQ K U D H q ψ L hU a a := by
  obtain ⟨v,B,hv,hvc,hvr⟩ := hc a
  have hb := h (U a) v B hv hvc hvr (D a) (hD a) (H a a) (hH a) q ψ A hq hqc hψ hq0
  convert hb using 1
  change N*(bochnerTestForm μ hQ (-K) (H a a) ψ+weightedLaplacianPair μ q (D a) (D a)+
    (1/2:ℝ)*(weightedGamma μ hQ (D a) (U a) ψ+weightedGamma μ hQ (D a) (U a) ψ)) = _
  ring

/-- Scalar weak BE identifies the dimensional density of the actual
full bilinear measure on every compact interior set. -/
theorem ScalarDimensionalBochner.regular_density [SigmaFinite μ] [SecondCountableTopology X]
    [IsFiniteMeasureOnCompacts μ] {K N : ℝ} (h : ScalarDimensionalBochner μ hQ K N)
    {m : ℕ} (U : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    (hc : ∀ a, ∃ (v : X → ℝ) (A : ℝ≥0), LipschitzWith A v ∧
      HasCompactSupport v ∧ SobolevSpace.toLp μ hQ (U a) =ᵐ[μ] v)
    (hD : ∀ a, IsWeakLaplacian μ hQ (U a) (D a))
    (hH : ∀ a, SobolevSpace.toLp μ hQ (H a a) =ᵐ[μ] localGamma μ hQ (U a) (U a))
    {Ω S : Set X} (M : PositiveBilinearMeasure X (Euclidean m))
    (hM : ∀ (a : Euclidean m) (ψ : SobolevSpace μ hQ) (q : X →ᵇ ℝ),
      HasCompactSupport (q : X → ℝ) → tsupport q ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q →
      (∫ x, q x ∂M.measure a)=regularBochnerForm μ hQ K U D H q ψ L hU a a)
    (hS : MeasurableSet S) (χ : X →ᵇ ℝ) {A : ℝ≥0} (hχ : LipschitzWith A χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : 0≤χ) (hχ1 : ∀ x∈S, χ x=1) :
    ∀ a, ∀ᵐ x ∂μ.restrict S,
      (laplacianCoordinateForm μ D x a)^2≤N*bochnerRadonDensity μ M x a a := by
  apply dimensional_bilinear_density_of_tests μ M D N hS χ hχ hχc hχΩ hχ0 hχ1
  intro a q hq
  let ψ := compactTestSobolev μ hQ Ω q
  have hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] (q : X →ᵇ ℝ) := compactTestSobolev_coe μ hQ Ω q
  obtain ⟨A,hA,hqc,hqΩ⟩ := q.property
  rw [hM a ψ q hqc hqΩ hψ]
  exact h.regular_form μ hQ U D H L hU hc hD hH a q ψ A hA hqc hψ hq

end RegularPointCoordinates

end

end OAI
