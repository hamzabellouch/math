import OAI.Geometry.RCD.Harmonic.RadialCompactnessSequence
import OAI.Geometry.RCD.Sobolev.ActualEulerLimit
import OAI.Geometry.RCD.Sobolev.PoissonHarmonicLimitSubsequence
import OAI.Geometry.RCD.Sobolev.EulerCoefficientSubsequence
import OAI.Geometry.RCD.Harmonic.ProjectionLimitContradiction

namespace OAI

/-! # The compactness contradiction for normalized projection residuals -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- There is no normalized orthogonal Euler countersequence satisfying
the actual analytic preconditions of Ambrosio--Honda compactness. The
coefficient subsequence is extracted after the joint function limit, so
all pairings and the nonzero norm refer to one and the same limit. -/
theorem no_euler_countersequence {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hcompact : LocalPoissonHarmonicCompactnessInput hX) (hn : 2 ≤ n)
    {S : ℝ} (hS : 0 < S) (q : RadialCompactnessSequence hX S)
    (B : ℕ → ℝ)
    (hf : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball (q.center i) (S * q.radius i)),
      localGamma (hausdorff n X) hX.quadratic (q.radialFunction i) (q.radialFunction i) x ≤ B i)
    (e : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (b : ℕ → Euclidean n) (k : ℕ → ℝ) {C : ℝ} (hcoeff : ∀ i, ‖b i‖ + |k i| ≤ C)
    (he : Tendsto (fun i => ‖normalizeLocalL2 (hausdorff n X) (ball (q.center i) (S * q.radius i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (q.center i) (S * q.radius i)) (e i))‖)
      atTop (𝓝 0))
    (hid : ∀ i,
      q.radius i ^ 2 • localRadialDerivative (hausdorff n X) hX.quadratic
        (ball (q.center i) (S * q.radius i)) (q.radialFunction i) (hf i) (q.harmonicFunction i) =
      SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (q.center i) (S * q.radius i)) (q.harmonicFunction i) +
        (∑ j, b i j • SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
          (ball (q.center i) (S * q.radius i)) (q.coordinates i j)) +
        k i • restrictedOne (hausdorff n X) (ball (q.center i) (S * q.radius i))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) +
        SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
          (ball (q.center i) (S * q.radius i)) (e i))
    {ρ c : ℝ} (hρ : 0 < ρ) (hρS : ρ < S) (hc : c ≠ 0)
    (hnorm : Tendsto (fun i =>
      ⟪localAffineMomentFamily (hausdorff n X) hX.quadratic (q.coordinates i) (q.harmonicFunction i)
          (ball (q.center i) (ρ * q.radius i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) none,
        localAffineMomentFamily (hausdorff n X) hX.quadratic (q.coordinates i) (q.harmonicFunction i)
          (ball (q.center i) (ρ * q.radius i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) none⟫_ℝ)
      atTop (𝓝 c))
    (horth : ∀ i j,
      ⟪localAffineMomentFamily (hausdorff n X) hX.quadratic (q.coordinates i) (q.harmonicFunction i)
          (ball (q.center i) (ρ * q.radius i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) none,
        localAffineMomentFamily (hausdorff n X) hX.quadratic (q.coordinates i) (q.harmonicFunction i)
          (ball (q.center i) (ρ * q.radius i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (some j)⟫_ℝ = 0) :
    False := by
  obtain ⟨t₁, ht₁, model, hlimit⟩ := hcompact.extract_sequence hn hS q
  obtain ⟨t₂, ht₂, L, kLimit, hL, hk⟩ :=
    euler_coefficient_subsequence (b ∘ t₁) (k ∘ t₁) (fun i => hcoeff (t₁ i))
  let t := t₁ ∘ t₂
  have ht : StrictMono t := ht₁.comp ht₂
  have hlimit' := hlimit.subsequence t₂ ht₂
  change PoissonHarmonicLimit hX S (q.center ∘ t) (q.radius ∘ t) (q.coordinates ∘ t)
    (q.coordinateValues ∘ t) (q.harmonicFunction ∘ t) (q.radialFunction ∘ t) model at hlimit'
  have hEuler := hlimit'.euler_equation hS (fun i => (q.measured (t i)).measurable)
    (fun i j => q.representative (t i) j) (B ∘ t) (fun i => hf (t i)) (e ∘ t)
    (fun i j => b (t i) j) (k ∘ t) L kLimit hL hk
    (he.comp ht.tendsto_atTop) (fun i => hid (t i))
  exact hlimit'.no_nonzero_orthogonal_euler_limit hS hρ hρS L kLimit hEuler hc
    (hnorm.comp ht.tendsto_atTop) (fun i j => horth (t i) j)

end RegularPointCoordinates

end

end OAI
