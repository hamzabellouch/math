import OAI.Geometry.RCD.Harmonic.HarmonicMomentCompactnessInput
import OAI.Geometry.RCD.Sobolev.ConstantLaplacianBochnerInput

namespace OAI

/-! # local compactness including radial gradient pairings

Ambrosio--Honda, *Local spectral convergence in RCD*(K,N) spaces* (2018),
Theorems 4.2, 4.4 and 4.6(2), Corollaries 4.3 and 4.5. This specialization
retains one harmonic function and one bounded-Laplacian function converging
in value to the squared Euclidean radius. The local gradient bound for the
latter and the harmonic energy bound give the L2 bound required in 4.6(2).
The conclusion records weak test pairings and finite value moments only.
-/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace Topology ContDiff

noncomputable section
namespace RegularPointCoordinates

def InteriorSmoothTest (n : ℕ) (S : ℝ) (ψ : Euclidean n → ℝ) : Prop :=
  ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ ball 0 S

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Precisely the weak pairings retained from the local strong/weak
Sobolev convergence theorem, with the physical radius factors explicit. -/
structure PoissonHarmonicLimit {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (S : ℝ) (p : ℕ → X) (r : ℕ → ℝ)
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (V : ℕ → X → Euclidean n)
    (w f : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (model : EuclideanHarmonicModel n S) : Prop where
  moments : ∀ ρ : ℝ, 0 < ρ → ∀ hρ : ρ < S, ∀ i j,
    Tendsto (fun k =>
      ⟪localAffineMomentFamily (hausdorff n X) hX.quadratic (u k) (w k)
          (ball (p k) (ρ * r k)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) i,
        localAffineMomentFamily (hausdorff n X) hX.quadratic (u k) (w k)
          (ball (p k) (ρ * r k)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) j⟫_ℝ)
      atTop (𝓝 ⟪model.moments hρ.le i, model.moments hρ.le j⟫_ℝ)
  tests : ∀ ψ : Euclidean n → ℝ, InteriorSmoothTest n S ψ →
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S * r k)))⁻¹ *
      ∫ x in ball (p k) (S * r k), ψ (V k x) *
        (r k ^ 2 * localGamma (hausdorff n X) hX.quadratic (f k) (w k) x) ∂hausdorff n X)
      atTop (𝓝 ((volume.real (ball (0 : Euclidean n) S))⁻¹ *
        ∫ z in ball 0 S, ψ z * fderiv ℝ model.value z z)) ∧
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S * r k)))⁻¹ *
      ∫ x in ball (p k) (S * r k), ψ (V k x) *
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x ∂hausdorff n X)
      atTop (𝓝 ((volume.real (ball (0 : Euclidean n) S))⁻¹ *
        ∫ z in ball 0 S, ψ z * model.value z)) ∧
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S * r k)))⁻¹ *
      ∫ x in ball (p k) (S * r k), ψ (V k x) ∂hausdorff n X)
      atTop (𝓝 ((volume.real (ball (0 : Euclidean n) S))⁻¹ *
        ∫ z in ball 0 S, ψ z)) ∧
    ∀ j, Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S * r k)))⁻¹ *
      ∫ x in ball (p k) (S * r k), ψ (V k x) * V k x j ∂hausdorff n X)
      atTop (𝓝 ((volume.real (ball (0 : Euclidean n) S))⁻¹ *
        ∫ z in ball 0 S, ψ z * z j))

/-- A bounded-Laplacian radial sequence and an arbitrary bounded harmonic
sequence have joint local limits. All assumptions are analytic bounds;
the projected Euler equation is deliberately absent. -/
def LocalPoissonHarmonicCompactnessInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∀ S : ℝ, 0 < S → ∀ (p : ℕ → X) (r ε : ℕ → ℝ),
    (∀ k, 0 < r k) → (∀ k, -1 ≤ K * r k ^ 2) →
    (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
  ∀ (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (V : ℕ → X → Euclidean n)
    (w f : ℕ → SobolevSpace (hausdorff n X) hX.quadratic),
    (∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k)) →
    (∀ k j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k j) =ᵐ[
      (hausdorff n X).restrict (ball (p k) (S * r k))] fun x => V k x j) →
    (∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S * r k)) (w k)) →
    (∀ k, ‖normalizeLocalL2 (hausdorff n X) (ball (p k) (S * r k))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (p k) (S * r k)) (w k))‖ ≤ 1) →
    (∀ ρ : ℝ, 0 < ρ → ρ < S → ∃ C : ℝ, 0 ≤ C ∧ ∀ k,
      r k ^ 2 * ((hausdorff n X).real (ball (p k) (S * r k)))⁻¹ *
        (∫ x in ball (p k) (ρ * r k), localGamma (hausdorff n X) hX.quadratic
          (w k) (w k) x ∂hausdorff n X) ≤ C) →
    (∃ (A : ℝ) (a : ℕ → ℝ), 0 ≤ A ∧ ∀ k,
      |a k| ≤ A ∧
      IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball (p k) (S * r k))
        (f k) (a k / r k ^ 2) ∧
      ‖normalizeLocalL2 (hausdorff n X) (ball (p k) (S * r k))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (p k) (S * r k)) (f k))‖ ≤ A ∧
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S * r k)),
        r k ^ 2 * localGamma (hausdorff n X) hX.quadratic (f k) (f k) x ≤ A) →
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S * r k)))⁻¹ *
      ∫ x in ball (p k) (S * r k),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic (f k) x - ‖V k x‖ ^ 2 / 2) ^ 2
          ∂hausdorff n X) atTop (𝓝 0) →
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∃ model : EuclideanHarmonicModel n S,
      PoissonHarmonicLimit hX S (p ∘ t) (r ∘ t) (u ∘ t) (V ∘ t) (w ∘ t) (f ∘ t) model

end RegularPointCoordinates

end

end OAI
