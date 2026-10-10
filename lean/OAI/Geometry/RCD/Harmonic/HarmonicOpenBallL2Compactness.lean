import OAI.Geometry.RCD.Harmonic.HarmonicOpenBallCompactness
import OAI.Geometry.RCD.Coordinates.NormalizedUniformL2
import OAI.Geometry.RCD.Sobolev.HarmonicGradientConstruction

namespace OAI

/-! # Actual strong local L2 compactness on the full limiting ball

The continuous local limit has a measurable zero extension. The same
subsequence converges in normalized L2 on every strict interior ball.
-/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem measurable_zero_extension_ball {n : ℕ} {S : ℝ} {g : Euclidean n → ℝ}
    (hg : ContinuousOn g (ball 0 S)) (hz : ∀ z, S≤‖z‖ → g z=0) : Measurable g := by
  classical
  have he : (ball (0:Euclidean n) S).piecewise g (fun _ => 0)=g := by
    funext z
    by_cases h : z∈ball (0:Euclidean n) S
    · simp only [piecewise_eq_of_mem _ _ _ h]
    · have hnorm : S≤‖z‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using h
      simp only [piecewise_eq_of_notMem _ _ _ h,hz z hnorm]
  rw [← he]
  exact hg.measurable_piecewise continuous_const.continuousOn measurableSet_ball

theorem NoncollapsedRCD.open_ball_harmonic_L2_compactness {K : ℝ} {n : ℕ}
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
      ∀ ρ : ℝ, 0<ρ → ρ<S →
        Tendsto (fun k => ((hausdorff n X).real (ball (p (a k)) (ρ*r (a k))))⁻¹*
          ∫ x in ball (p (a k)) (ρ*r (a k)),
            (SobolevSpace.toLp (hausdorff n X) hX.quadratic (u (a k)) x-g (v (a k) x))^2
              ∂hausdorff n X) atTop (𝓝 0) := by
  obtain ⟨g,a,ha,hgc,hgL,hg0,hconv⟩ := harmonic_open_ball_value_compactness hX hn
    hX.harmonicMeanValueInput (hX.harmonicGradientInput hn (p 0)) hS p r ε hr hcurv
    hε hε1 hεlim v (fun k => (hv k).metric) u hu hnorm
  have hgm := measurable_zero_extension_ball hgc hg0
  refine ⟨g,a,ha,hgm,hgc,hgL,?_⟩
  intro ρ hρ hρS
  let μ := hausdorff n X
  let ν : ℕ → Measure X := fun k => μ.restrict (ball (p (a k)) (ρ*r (a k)))
  let : ∀ k, IsFiniteMeasure (ν k) := fun k =>
    ⟨by simpa only [ν,Measure.restrict_apply_univ] using (hX.finiteOnBounded
      (ball (p (a k)) (ρ*r (a k))) isBounded_ball)⟩
  have hmass (k : ℕ) : 0<(ν k).real univ := by
    change 0<(μ.restrict (ball (p (a k)) (ρ*r (a k)))).real univ
    rw [Measure.real,Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hρ (hr (a k)))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  let F := fun k x => SobolevSpace.toLp μ hX.quadratic (u (a k)) x-g (v (a k) x)
  have hFm (k : ℕ) : AEStronglyMeasurable (F k) (ν k) :=
    ((Lp.aestronglyMeasurable (SobolevSpace.toLp μ hX.quadratic (u (a k)))).sub
      (hgm.comp (hv (a k)).measurable).aestronglyMeasurable).mono_measure Measure.restrict_le_self
  have hFu : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ᵐ x ∂ν k, |F k x|≤η := by
    intro η hη
    filter_upwards [hconv ρ hρ hρS η hη] with k hk
    exact hk.mono fun x hx => hx.le
  have hh := normalized_sq_mean_tendsto_zero ν hmass F hFm hFu
  simpa only [F,ν,Measure.real,Measure.restrict_apply_univ] using hh

end RegularPointCoordinates

end

end OAI
