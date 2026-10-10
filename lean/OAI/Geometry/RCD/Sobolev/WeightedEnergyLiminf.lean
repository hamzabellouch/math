import OAI.Geometry.RCD.Sobolev.WeightedEnergyLower

namespace OAI

/-! # Eventual sharp lower bounds for every compact nonnegative weight -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.weighted_energy_eventual_lower {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S ρ τ R : ℝ} (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (hτR : τ<R) (hRS : R<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g : Euclidean n → ℝ) (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤δ)
    (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0≤φ z) (hs : Function.support φ⊆ball 0 ρ)
    {M : ℝ} (hM : 0≤M)
    (hbound : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M)
    : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z, φ z*‖fderiv ℝ g z‖^2)-δ≤
        (r k^2/(hausdorff n X).real (ball (p k) (S*r k)))*
          (∫ x in closedBall (p k) (R*r k), φ (v k x)*localGamma (hausdorff n X) hX.quadratic
            (w k) (w k) x ∂hausdorff n X) := by
  intro δ hδ
  by_contra hnot
  have hbad := (not_eventually.mp hnot).and_eventually hbound
  obtain ⟨t,ht,hbad⟩ := extraction_of_frequently_atTop hbad
  let V := volume.real (ball (0:Euclidean n) S)
  let I := ∫ z, φ z*‖fderiv ℝ g z‖^2
  have hV : 0<V := ENNReal.toReal_pos (measure_ball_pos volume 0 hS).ne' measure_ball_lt_top.ne
  have hlow := hX.weighted_energy_lower_of_curvature_sequence hn hS hτ hρτ hτR hRS
    (p ∘ t) (r ∘ t) (ε ∘ t) (v ∘ t) (fun k => hr (t k))
    (fun k => hcurv (t k)) (fun k => hε (t k)) (fun k => hε1 (t k))
    (hεlim.comp ht.tendsto_atTop) (fun k => hv (t k)) (w ∘ t) g hg
    (fun W hW hWS η hη => ht.tendsto_atTop.eventually (hconv W hW hWS η hη))
    φ hφ hs hM (fun k => (hbad k).2) (C := V⁻¹*I-δ) (by
      intro η hη
      filter_upwards [] with k
      have hk := lt_of_not_ge (hbad k).1
      exact hk.le.trans (le_add_of_nonneg_right hη.le))
  have he := hlow.2
  change I≤V*(V⁻¹*I-δ) at he
  have hcancel : V*(V⁻¹*I)=I := by rw [← mul_assoc,mul_inv_cancel₀ hV.ne',one_mul]
  nlinarith [mul_pos hV hδ]

end RegularPointCoordinates

end

end OAI
