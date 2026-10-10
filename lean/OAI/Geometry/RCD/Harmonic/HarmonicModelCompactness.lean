import OAI.Geometry.RCD.Harmonic.CurvatureHarmonicLimit
import OAI.Geometry.RCD.Harmonic.HarmonicValueAffineCompactness

namespace OAI

/-! # Actual Euclidean harmonic models under the original curvature-scale bound

The normalized harmonic model, finite affine moments and smooth value
pairings are constructed without any restriction on the limiting radii.
-/

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_model_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S : ℝ} (hS : 0<S) (p : ℕ → X) (r ε : ℕ → ℝ)
    (hr : ∀ k, 0<r k)
    (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n) (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (hrep : ∀ k j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k j)=ᵐ[
      (hausdorff n X).restrict (ball (p k) (S*r k))] fun x => v k x j)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤1) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∃ model : EuclideanHarmonicModel n S,
      (∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L model.value (closedBall 0 W)) ∧
      (∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (a k)) (W*r (a k))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x-model.value (v (a k) x)|≤δ) ∧
      (∀ ρ : ℝ, 0<ρ → ∀ hρS : ρ<S, ∀ i j,
        Tendsto (fun k =>
          inner ℝ (localAffineMomentFamily (hausdorff n X) hX.quadratic (u (a k)) (w (a k))
              (ball (p (a k)) (ρ*r (a k))) (hX.finiteOnBounded _ isBounded_ball).ne i)
            (localAffineMomentFamily (hausdorff n X) hX.quadratic (u (a k)) (w (a k))
              (ball (p (a k)) (ρ*r (a k))) (hX.finiteOnBounded _ isBounded_ball).ne j))
          atTop (𝓝 (inner ℝ (model.moments hρS.le i) (model.moments hρS.le j)))) ∧
      ∀ ψ : Euclidean n → ℝ, InteriorSmoothTest n S ψ →
        Tendsto (fun k => ((hausdorff n X).real (ball (p (a k)) (S*r (a k))))⁻¹*
          ∫ x in ball (p (a k)) (S*r (a k)), ψ (v (a k) x)*
            SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x ∂hausdorff n X)
          atTop (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
            ∫ z in ball 0 S, ψ z*model.value z)) := by
  obtain ⟨a,ha,g,hLp,hnormal,hgm,hgc,hgL,hconv,hmom,htests⟩ :=
    hX.harmonic_value_affine_compactness hn hS p r ε hr hcurv hε hε1 hεlim u v w hv hrep hw hnorm
  have hweak := hX.harmonic_value_limit_weak_of_curvature hn hS (p ∘ a) (r ∘ a) (ε ∘ a)
    (fun k => hr (a k)) (fun k => hcurv (a k))
    (fun k => hε (a k)) (fun k => hε1 (a k)) (hεlim.comp ha.tendsto_atTop)
    (v ∘ a) (w ∘ a) (fun k => hv (a k)) (fun k => hw (a k)) (fun k => hnorm (a k)) g hgL hconv
  let model : EuclideanHarmonicModel n S :=
    ⟨g,continuous_weak_harmonic hgc hweak,hLp,hnormal⟩
  refine ⟨a,ha,model,hgL,hconv,?_,htests⟩
  intro ρ hρ hρS i j
  exact hmom ρ hρ hρS i j

end RegularPointCoordinates

end

end OAI
