import OAI.Geometry.RCD.Metric.MeasuredValueLimitNorm
import OAI.Geometry.RCD.Harmonic.HarmonicAffineImprovement

namespace OAI

/-! # The exact Euclidean L2 normalization of an actual Sobolev value limit -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.value_limit_normalized {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S : ℝ} (hS : 0<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (u k)≤1)
    (g : Euclidean n → ℝ) (hgm : Measurable g)
    (hg : ∀ ρ<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 ρ))
    (hconv : ∀ ρ : ℝ, 0<ρ → ρ<S → ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (ρ*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x-g (v k x)|≤η) :
    ∃ hLp : MemLp g 2 (volume.restrict (ball 0 S)),
      ‖normalizeLocalL2 volume (ball 0 S) measure_ball_ne_top (hLp.toLp g)‖≤1 := by
  obtain ⟨hLp,hI⟩ := measured_value_limit_normalized (hausdorff n X) hS p r ε v hr hεlim hv
    (fun k => (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k)) g hgm
    (fun k => (Lp.memLp (SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k))).mono_measure
      Measure.restrict_le_self)
    (fun k => sobolev_mean_sq_le_one_of_normalized (hausdorff n X) hX.quadratic
      (ball (p k) (S*r k)) (hX.finiteOnBounded _ isBounded_ball).ne (u k) (hnorm k)) hg hconv
  refine ⟨hLp,?_⟩
  have hsq := normalizeLocalL2_norm_sq volume (ball (0:Euclidean n) S)
    measure_ball_ne_top (hLp.toLp g)
  have he : (∫ z in ball 0 S, ((hLp.toLp g) z)^2)=∫ z in ball 0 S, (g z)^2 := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hLp] with z hz
    rw [hz]
  rw [he] at hsq
  nlinarith [norm_nonneg (normalizeLocalL2 volume (ball 0 S) measure_ball_ne_top (hLp.toLp g))]

end RegularPointCoordinates

end

end OAI
