import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicModel
import OAI.Geometry.RCD.Metric.MeasuredApproximation

namespace OAI

/-! # The local harmonic-compactness input, restricted to finite moments

Ambrosio--Honda (2018), Local spectral convergence in RCD*(K,N) spaces,
Theorem 4.2, Theorem 4.4 and Corollary 4.5, specialized to a Euclidean
measured limit. Strong local L² convergence implies convergence of the
pairings with constants and the bounded coordinate functions. The
hypothesis below retains the local rescaled H¹ bound needed by those
theorems. It asserts neither an affine approximation nor a chart.
-/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Only the normalized moments of one harmonic function and the finite
coordinate family are retained from the published local compactness theorem.
All target functions are genuine Sobolev functions of the original space. -/
def LocalHarmonicMomentCompactnessInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) : Prop :=
  ∀ S : ℝ, 0 < S →
    ∀ (p : ℕ → X) (r ε : ℕ → ℝ), (∀ k, 0 < r k) →
      (∀ k, -1 ≤ K * r k ^ 2) → (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
    ∀ (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
      (v : ℕ → X → Euclidean n)
      (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic),
      (∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k)) →
      (∀ k i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k i) =ᵐ[
        (hausdorff n X).restrict (ball (p k) (S * r k))] fun x => v k x i) →
      (∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
        (ball (p k) (S * r k)) (w k)) →
      (∀ k, ‖normalizeLocalL2 (hausdorff n X) (ball (p k) (S * r k))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
          (ball (p k) (S * r k)) (w k))‖ ≤ 1) →
      (∀ ρ : ℝ, 0 < ρ → ρ < S → ∃ C : ℝ, 0 ≤ C ∧ ∀ k,
        r k ^ 2 * ((hausdorff n X).real (ball (p k) (S * r k)))⁻¹ *
          (∫ x in ball (p k) (ρ * r k), localGamma (hausdorff n X) hX.quadratic
            (w k) (w k) x ∂hausdorff n X) ≤ C) →
      ∃ t : ℕ → ℕ, StrictMono t ∧ ∃ model : EuclideanHarmonicModel n S,
        ∀ ρ : ℝ, 0 < ρ → ∀ hρS : ρ < S, ∀ i j,
          Tendsto (fun k =>
            ⟪localAffineMomentFamily (hausdorff n X) hX.quadratic (u (t k)) (w (t k))
                (ball (p (t k)) (ρ * r (t k)))
                (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) i,
              localAffineMomentFamily (hausdorff n X) hX.quadratic (u (t k)) (w (t k))
                (ball (p (t k)) (ρ * r (t k)))
                (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) j⟫_ℝ) atTop
            (𝓝 ⟪model.moments hρS.le i, model.moments hρS.le j⟫_ℝ)

end RegularPointCoordinates

end

end OAI
