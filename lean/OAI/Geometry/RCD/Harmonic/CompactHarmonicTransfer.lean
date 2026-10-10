import OAI.Geometry.RCD.Harmonic.CompactMixedTransfer
import OAI.Geometry.RCD.Sobolev.SupportedWeightedGamma
import OAI.Geometry.RCD.Sobolev.RescaledLocalEnergyBound
import OAI.Geometry.RCD.Sobolev.MeasuredRadialCutoff

namespace OAI

/-! # Strong local harmonic recovery preserves compact-test mixed integrals -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_harmonic_transfer {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S c a b R : ℝ}
    (hS : 0<S) (hca : c<a) (hab : a<b) (hbR : b<R) (hRS : R<S)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (V : ℕ → X → Euclidean n) (hV : ∀ k, Measurable (V k))
    (u w q : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (F : Euclidean n →ᵇ ℝ) {Q : ℝ}
    (hub : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r k^2*localGamma (hausdorff n X) hX.quadratic (u k) (u k) x≤Q^2)
    (huz : ∀ k, ∀ᵐ x ∂hausdorff n X, x∉ball (p k) (c*r k) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x=0)
    (herror : Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (R*r k), (nestedBallCutoff (p k) (a*r k) (b*r k) x)^2*
        localGamma (hausdorff n X) hX.quadratic (w k-q k) (w k-q k) x ∂hausdorff n X)
      atTop (𝓝 0)) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (S*r k), F (V k x)*localGamma (hausdorff n X) hX.quadratic
        (u k) (w k) x ∂hausdorff n X)-
      r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (S*r k), F (V k x)*localGamma (hausdorff n X) hX.quadratic
        (u k) (q k) x ∂hausdorff n X)) atTop (𝓝 0) := by
  let μ := hausdorff n X
  let Ω := fun k => ball (p k) (R*r k)
  let U := fun k => ball (p k) (S*r k)
  let A := fun k => ball (p k) (c*r k)
  let C := fun k => r k^2*(μ.real (U k))⁻¹
  let χ := fun k => nestedBallCutoff (p k) (a*r k) (b*r k)
  have hm (k : ℕ) : 0<μ.real (U k) := ENNReal.toReal_pos
    (hX.fullSupport _ _ (mul_pos hS (hr k))).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hzero (k : ℕ) : ∀ᵐ x ∂μ, x∉Ω k → SobolevSpace.toLp μ hX.quadratic (u k) x=0 :=
    (huz k).mono fun x hx hn => hx (fun hy => hn
      ((ball_subset_ball (mul_le_mul_of_nonneg_right (hca.trans (hab.trans hbR)).le (hr k).le)) hy))
  have henergy : ∀ᶠ k in atTop, C k*(∫ x in Ω k, localGamma μ hX.quadratic (u k) (u k) x ∂μ)≤Q^2 := by
    filter_upwards [hub] with k hk
    have hh := rescaled_local_energy_bound μ hX.quadratic (u k)
      (ball_subset_ball (mul_le_mul_of_nonneg_right hRS.le (hr k).le))
      (hX.finiteOnBounded (U k) isBounded_ball).ne (hm k) (sq_nonneg Q) (ae_restrict_of_ae hk)
    simpa only [C,div_eq_mul_inv] using hh
  have he := compact_mixed_transfer μ hX.quadratic Ω A C
    (fun k => mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (hm k).le)) u w q
    (fun k x => F (V k x)) χ (norm_nonneg F) (sq_nonneg Q)
    (fun k => (F.continuous.measurable.comp (hV k)).aestronglyMeasurable)
    (fun k => (nestedBallCutoff_lipschitz (p k) (mul_lt_mul_of_pos_right hab (hr k))).continuous.aestronglyMeasurable)
    (fun k => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (V k x))
    (fun k => Eventually.of_forall fun x => by
      rw [abs_of_nonneg (nestedBallCutoff_bounds _ _ _ _).1]
      exact (nestedBallCutoff_bounds _ _ _ _).2)
    (fun k x hx => nestedBallCutoff_eq_one (p k) (mul_lt_mul_of_pos_right hab (hr k))
      (by rw [dist_comm]; exact hx.le.trans (mul_le_mul_of_nonneg_right hca.le (hr k).le))) huz henergy herror
  apply he.congr'
  apply Eventually.of_forall
  intro k
  have hsub : Ω k⊆U k := ball_subset_ball (mul_le_mul_of_nonneg_right hRS.le (hr k).le)
  dsimp only [C]
  rw [supported_weighted_gamma μ hX.quadratic (u k) (w k) (fun x => F (V k x)) hsub (hzero k),
    supported_weighted_gamma μ hX.quadratic (u k) (q k) (fun x => F (V k x)) hsub (hzero k)]

end RegularPointCoordinates

end

end OAI
