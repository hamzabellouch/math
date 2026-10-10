import OAI.Geometry.RCD.Harmonic.AffineMomentConvergence
import OAI.Geometry.RCD.Sobolev.HarmonicValueTestCompactness
import OAI.Geometry.RCD.Coordinates.ValueLimitNormalization

namespace OAI

/-! # Actual normalized harmonic value limits and every finite affine moment

The limit is constructed on the entire open ball from the original RCD
sequence. This theorem does not assert Euclidean harmonicity or convergence
of gradient pairings; those remain the analytic identification step.
-/

open Set Metric Filter MeasureTheory
open scoped Topology InnerProductSpace NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_value_affine_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S : ℝ} (hS : 0<S) (p : ℕ → X) (r ε : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n) (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (hrep : ∀ k j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k j)=ᵐ[
      (hausdorff n X).restrict (ball (p k) (S*r k))] fun x => v k x j)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤1) :
    ∃ (a : ℕ → ℕ), StrictMono a ∧ ∃ (g : Euclidean n → ℝ)
      (hLp : MemLp g 2 (volume.restrict (ball 0 S))),
      ‖normalizeLocalL2 volume (ball 0 S) measure_ball_ne_top (hLp.toLp g)‖≤1 ∧
      Measurable g ∧ ContinuousOn g (ball 0 S) ∧
      (∀ τ<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 τ)) ∧
      (∀ ρ : ℝ, 0<ρ → ρ<S → ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (a k)) (ρ*r (a k))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x-g (v (a k) x)|≤η) ∧
      (∀ ρ : ℝ, 0<ρ → ∀ hρS : ρ<S, ∀ i j,
        Tendsto (fun k =>
          ⟪localAffineMomentFamily (hausdorff n X) hX.quadratic (u (a k)) (w (a k))
              (ball (p (a k)) (ρ*r (a k))) (hX.finiteOnBounded _ isBounded_ball).ne i,
            localAffineMomentFamily (hausdorff n X) hX.quadratic (u (a k)) (w (a k))
              (ball (p (a k)) (ρ*r (a k))) (hX.finiteOnBounded _ isBounded_ball).ne j⟫_ℝ)
          atTop (𝓝 ⟪euclideanValueMoments g hLp hρS.le i,
            euclideanValueMoments g hLp hρS.le j⟫_ℝ)) ∧
      ∀ ψ : Euclidean n → ℝ, InteriorSmoothTest n S ψ →
        Tendsto (fun k => ((hausdorff n X).real (ball (p (a k)) (S*r (a k))))⁻¹*
          ∫ x in ball (p (a k)) (S*r (a k)), ψ (v (a k) x)*
            SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x ∂hausdorff n X)
          atTop (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
            ∫ z in ball 0 S, ψ z*g z)) := by
  obtain ⟨g,a,ha,hgm,hgc,hgL,hconv,htests⟩ :=
    hX.open_ball_harmonic_test_compactness hn hS p r ε hr hcurv hε hε1 hεlim v hv w hw hnorm
  have hconv' : ∀ ρ : ℝ, 0<ρ → ρ<S → ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (a k)) (ρ*r (a k))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x-g (v (a k) x)|≤η := by
    intro ρ hρ hρS η hη
    exact (hconv ρ hρ hρS η hη).mono fun _ hk => hk.mono fun _ hx => hx.le
  obtain ⟨hLp,hgNorm⟩ := hX.value_limit_normalized hS (p ∘ a) (r ∘ a) (ε ∘ a) (v ∘ a)
    (fun k => hr (a k)) (hεlim.comp ha.tendsto_atTop) (fun k => hv (a k))
    (w ∘ a) (fun k => hnorm (a k)) g hgm hgL hconv'
  refine ⟨a,ha,g,hLp,hgNorm,hgm,hgc,hgL,hconv',?_,htests⟩
  exact hX.affine_value_moments_of_limit hS (p ∘ a) (r ∘ a) (ε ∘ a)
    (fun k => hr (a k)) (u ∘ a) (v ∘ a) (w ∘ a) (fun k => hv (a k))
    (hεlim.comp ha.tendsto_atTop) (fun k j => hrep (a k) j) g hLp hgL hconv'

end RegularPointCoordinates

end

end OAI
