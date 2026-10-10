import OAI.Geometry.RCD.Coordinates.OuterNormalizedSquareLimit

namespace OAI

/-! # Annular value moments of the same actual Sobolev sequence -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.outer_normalized_annular_square_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S a b τ : ℝ} (hS : 0<S) (ha : 0<a)
    (hab : a<b) (hbτ : b<τ) (hτS : τ≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k)
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (hε : Tendsto ε atTop (𝓝 0))
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g : Euclidean n → ℝ) {L : ℝ≥0} (hg : LipschitzOnWith L g (closedBall 0 τ))
    (hu : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (b*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x-g (V k x)|≤η) :
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (b*r k) \ ball (p k) (a*r k),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x)^2 ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*∫ z in ball 0 b \ ball 0 a, (g z)^2)) := by
  have hua : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (a*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x-g (V k x)|≤η := by
    intro η hη
    exact (hu η hη).mono fun k hk => ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (mul_le_mul_of_nonneg_right hab.le (hr k).le)) hk
  have hi := hX.outer_normalized_square_limit hS ha (hab.trans hbτ) hτS p r ε V hr hV hε u g hg hua
  have ho := hX.outer_normalized_square_limit hS (ha.trans hab) hbτ hτS p r ε V hr hV hε u g hg hu
  have ht := ho.sub hi
  have hgb : IntegrableOn (fun z => (g z)^2) (ball 0 b) volume :=
    ((hg.continuousOn.pow 2).integrableOn_compact (isCompact_closedBall (0:Euclidean n) τ)).mono_set
      ((ball_subset_ball hbτ.le).trans ball_subset_closedBall)
  have he : (∫ z in ball 0 b \ ball 0 a, (g z)^2)=
      (∫ z in ball 0 b, (g z)^2)-(∫ z in ball 0 a, (g z)^2) :=
    setIntegral_sdiff measurableSet_ball hgb (ball_subset_ball hab.le)
  rw [he,mul_sub]
  convert ht using 1
  funext k
  rw [setIntegral_sdiff measurableSet_ball (Lp.memLp
    (SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k))).integrable_sq.restrict
    (ball_subset_ball (mul_le_mul_of_nonneg_right hab.le (hr k).le)),mul_sub]

end RegularPointCoordinates

end

end OAI
