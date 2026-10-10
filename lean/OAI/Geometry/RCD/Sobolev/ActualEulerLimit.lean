import OAI.Geometry.RCD.Sobolev.EulerPairingLimit
import OAI.Geometry.RCD.Sobolev.EuclideanEulerPairing
import OAI.Geometry.RCD.Sobolev.CompactTestPairing

namespace OAI

/-! # Passing the actual Sobolev Euler equation to the Euclidean limit -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Joint compactness, the actual projected Sobolev equation,
and a vanishing normalized error imply the limiting Euler equation.
There is no assumption of an Euler equation for the limiting model. -/
theorem PoissonHarmonicLimit.euler_equation {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    {S : ℝ} {p : ℕ → X} {r : ℕ → ℝ}
    {u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic}
    {V : ℕ → X → Euclidean n} {w f : ℕ → SobolevSpace (hausdorff n X) hX.quadratic}
    {model : EuclideanHarmonicModel n S} (hlimit : PoissonHarmonicLimit hX S p r u V w f model)
    (hS : 0 < S) (hV : ∀ i, Measurable (V i))
    (hrep : ∀ i j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i j) =ᵐ[
      (hausdorff n X).restrict (ball (p i) (S * r i))] fun x => V i x j)
    (B : ℕ → ℝ)
    (hf : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p i) (S * r i)),
      localGamma (hausdorff n X) hX.quadratic (f i) (f i) x ≤ B i)
    (e : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (ell : ℕ → Fin n → ℝ) (k : ℕ → ℝ)
    (L : Euclidean n →L[ℝ] ℝ) (kLimit : ℝ)
    (hL : ∀ j, Tendsto (fun i => ell i j) atTop (𝓝 (L (EuclideanSpace.single j 1))))
    (hk : Tendsto k atTop (𝓝 kLimit))
    (he : Tendsto (fun i => ‖normalizeLocalL2 (hausdorff n X) (ball (p i) (S * r i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (p i) (S * r i)) (e i))‖)
      atTop (𝓝 0))
    (hid : ∀ i,
      r i ^ 2 • localRadialDerivative (hausdorff n X) hX.quadratic (ball (p i) (S * r i))
        (f i) (hf i) (w i) =
      SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (p i) (S * r i)) (w i) +
        (∑ j, ell i j • SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
          (ball (p i) (S * r i)) (u i j)) +
        k i • restrictedOne (hausdorff n X) (ball (p i) (S * r i))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) +
        SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (p i) (S * r i)) (e i)) :
    ∀ x ∈ ball 0 S, fderiv ℝ model.value x x = model.value x + L x + kLimit := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := fun i => ball (p i) (S * r i)
  let hfin : ∀ i, μ (s i) ≠ ∞ := fun i => ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  let J := fun i => SobolevSpace.restrictLp μ hQ (s i)
  let W := fun i => normalizeLocalL2 μ (s i) (hfin i) (J i (w i))
  let U := fun i j => normalizeLocalL2 μ (s i) (hfin i) (J i (u i j))
  let E := fun i => normalizeLocalL2 μ (s i) (hfin i) (J i (e i))
  let One := fun i => normalizeLocalL2 μ (s i) (hfin i) (restrictedOne μ (s i) (hfin i))
  let D := fun i => r i ^ 2 • normalizeLocalL2 μ (s i) (hfin i)
    (localRadialDerivative μ hQ (s i) (f i) (hf i) (w i))
  have heq (i : ℕ) : D i = W i + ∑ j, ell i j • U i j + k i • One i + E i :=
    normalized_euler_identity μ (s i) (hfin i) (J i (w i)) (J i (e i))
      (localRadialDerivative μ hQ (s i) (f i) (hf i) (w i)) (restrictedOne μ (s i) (hfin i))
      (fun j => J i (u i j)) (ell i) (k i) (r i ^ 2) (hid i)
  apply euler_equation_of_average_pairings hS model.value model.harmonic.contDiffOn L kLimit
  intro ψ hψ
  let P := fun i => normalizeLocalL2 μ (s i) (hfin i)
    (compactTestLp μ (s i) (hfin i) (V i) (hV i) ψ hψ.1.continuous hψ.2.1)
  have hP (i : ℕ) : ‖P i‖ ≤ compactTestBound ψ hψ.1.continuous hψ.2.1 :=
    compactTestLp_normalized_norm μ (s i) (hfin i) (V i) (hV i) ψ hψ.1.continuous hψ.2.1
  have hDp (i : ℕ) : ⟪P i, D i⟫_ℝ = (μ.real (s i))⁻¹ *
      ∫ x in s i, ψ (V i x) * (r i ^ 2 * localGamma μ hQ (f i) (w i) x) ∂μ :=
    compactTest_radial_pairing μ hQ (s i) (hfin i) (V i) (hV i) ψ hψ.1.continuous hψ.2.1
      (f i) (w i) (hf i) (r i ^ 2)
  have hWp (i : ℕ) : ⟪P i, W i⟫_ℝ = (μ.real (s i))⁻¹ *
      ∫ x in s i, ψ (V i x) * SobolevSpace.toLp μ hQ (w i) x ∂μ :=
    compactTest_sobolev_pairing μ hQ (s i) (hfin i) (V i) (hV i) ψ hψ.1.continuous hψ.2.1 (w i)
  have hOp (i : ℕ) : ⟪P i, One i⟫_ℝ = (μ.real (s i))⁻¹ * ∫ x in s i, ψ (V i x) ∂μ :=
    compactTest_one_pairing μ (s i) (hfin i) (V i) (hV i) ψ hψ.1.continuous hψ.2.1
  have hUp (i : ℕ) (j : Fin n) : ⟪P i, U i j⟫_ℝ = (μ.real (s i))⁻¹ *
      ∫ x in s i, ψ (V i x) * V i x j ∂μ :=
    normalized_inner_of_representatives μ (s i) (hfin i) _ _ _ _
      (compactTestLp_coe μ (s i) (hfin i) (V i) (hV i) ψ hψ.1.continuous hψ.2.1)
      ((SobolevSpace.restrictLp_coe μ hQ (s i) (u i j)).trans (hrep i j))
  obtain ⟨hDlim, hWlim, hOlim, hUlim⟩ := hlimit.tests ψ hψ
  have hdlim : Tendsto (fun i => ⟪P i, D i⟫_ℝ) atTop
      (𝓝 ((volume.real (ball (0 : Euclidean n) S))⁻¹ * ∫ x in ball 0 S, ψ x * fderiv ℝ model.value x x)) := by
    simpa only [hDp] using hDlim
  have hwlim : Tendsto (fun i => ⟪P i, W i⟫_ℝ) atTop
      (𝓝 ((volume.real (ball (0 : Euclidean n) S))⁻¹ * ∫ x in ball 0 S, ψ x * model.value x)) := by
    simpa only [hWp] using hWlim
  have holim : Tendsto (fun i => ⟪P i, One i⟫_ℝ) atTop
      (𝓝 ((volume.real (ball (0 : Euclidean n) S))⁻¹ * ∫ x in ball 0 S, ψ x)) := by
    simpa only [hOp] using hOlim
  have hulim (j : Fin n) : Tendsto (fun i => ⟪P i, U i j⟫_ℝ) atTop
      (𝓝 ((volume.real (ball (0 : Euclidean n) S))⁻¹ * ∫ x in ball 0 S, ψ x * x j)) := by
    simpa only [hUp] using hUlim j
  exact euler_pairing_limit P D W One E U ell k heq hP he hdlim hwlim holim hulim hL hk

end RegularPointCoordinates

end

end OAI
