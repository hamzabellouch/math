import OAI.Geometry.RCD.Harmonic.HarmonicOpenBallL2Compactness
import OAI.Geometry.RCD.Metric.LocalizedMeasuredValueLimit
import OAI.Geometry.RCD.Sobolev.InteriorSmoothTestBounds

namespace OAI

/-! # Harmonic value limits against interior smooth tests

Normalized harmonic values converge against all compact interior smooth tests.
-/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.open_ball_harmonic_test_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S : ℝ} (hS : 0<S) (p : ℕ → X) (r ε : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (v : ℕ → X → Euclidean n)
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (u k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (u k)≤1) :
    ∃ (g : Euclidean n → ℝ) (a : ℕ → ℕ), StrictMono a ∧ Measurable g ∧
      ContinuousOn g (ball 0 S) ∧
      (∀ ρ<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 ρ)) ∧
      (∀ ρ : ℝ, 0<ρ → ρ<S → ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (a k)) (ρ*r (a k))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u (a k)) x-g (v (a k) x)|<η) ∧
      ∀ ψ : Euclidean n → ℝ, InteriorSmoothTest n S ψ →
        Tendsto (fun k => ((hausdorff n X).real (ball (p (a k)) (S*r (a k))))⁻¹*
          ∫ x in ball (p (a k)) (S*r (a k)), ψ (v (a k) x)*
            SobolevSpace.toLp (hausdorff n X) hX.quadratic (u (a k)) x ∂hausdorff n X)
          atTop (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
            ∫ z in ball 0 S, ψ z*g z)) := by
  obtain ⟨g,a,ha,hgc,hgL,hg0,hconv⟩ := harmonic_open_ball_value_compactness hX hn
    hX.harmonicMeanValueInput (hX.harmonicGradientInput hn (p 0)) hS p r ε hr hcurv
    hε hε1 hεlim v (fun k => (hv k).metric) u hu hnorm
  refine ⟨g,a,ha,measurable_zero_extension_ball hgc hg0,hgc,hgL,hconv,?_⟩
  intro ψ hψ
  obtain ⟨ρ,hρ,hρS,M,B,hψL,hψB,hψ0⟩ := hψ.metric_bounds hS
  let τ := (ρ+S)/2
  have hρτ : ρ<τ := by dsimp only [τ]; linarith
  have hτS : τ<S := by dsimp only [τ]; linarith
  have hτ : 0<τ := hρ.trans hρτ
  obtain ⟨L,hg⟩ := hgL τ hτS
  apply localized_measured_value_limit (hausdorff n X) hτ.le hρτ hτS.le
    (p ∘ a) (r ∘ a) (ε ∘ a) (v ∘ a) (fun k => hr (a k))
    (hεlim.comp ha.tendsto_atTop) (fun k => hv (a k))
    (fun k => (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr (a k)))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => SobolevSpace.toLp (hausdorff n X) hX.quadratic (u (a k))) g ψ
    ?_ hg hψL hψB hψ0 ?_
  · intro k
    change IntegrableOn (SobolevSpace.toLp (hausdorff n X) hX.quadratic (u (a k)))
      (ball (p (a k)) (S*r (a k))) (hausdorff n X)
    let : IsFiniteMeasure ((hausdorff n X).restrict (ball (p (a k)) (S*r (a k)))) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        (hX.finiteOnBounded (ball (p (a k)) (S*r (a k))) isBounded_ball)⟩
    exact MemLp.integrable (by norm_num)
      ((Lp.memLp (SobolevSpace.toLp (hausdorff n X) hX.quadratic (u (a k)))).mono_measure
        Measure.restrict_le_self)
  · intro η hη
    exact (hconv τ hτ hτS η hη).mono fun k hk => hk.mono fun x hx => hx.le

end RegularPointCoordinates

end

end OAI
