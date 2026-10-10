import OAI.Geometry.RCD.Sobolev.WeightedMixedEnergy

namespace OAI

/-! # Mixed energies of two actual compact test recoveries -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_recovery_mixed_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {S : ℝ} (hS : 0<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (u q : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    {ψ G : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ) (hG : InteriorSmoothTest n S G)
    (huv : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x-ψ (V k x)|≤δ)
    (hqv : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k) x-G (V k x)|≤δ)
    {M Q : ℝ} (hM : 0≤M) (hQ : 0≤Q)
    (hub : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r k^2*localGamma (hausdorff n X) hX.quadratic (u k) (u k) x≤M)
    (hqb : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r k^2*localGamma (hausdorff n X) hX.quadratic (q k) (q k) x≤Q)
    (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0≤φ z) (hs : tsupport φ⊆ball 0 S)
    (huenergy : Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), φ (V k x)*localGamma (hausdorff n X) hX.quadratic
        (u k) (u k) x ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*∫ z in ball 0 S, φ z*‖fderiv ℝ ψ z‖^2)))
    (hqenergy : Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), φ (V k x)*localGamma (hausdorff n X) hX.quadratic
        (q k) (q k) x ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*∫ z in ball 0 S, φ z*‖fderiv ℝ G z‖^2))) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), φ (V k x)*localGamma (hausdorff n X) hX.quadratic
        (u k) (q k) x ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
        ∫ z in ball 0 S, φ z*inner ℝ (gradient ψ z) (gradient G z))) := by
  obtain ⟨ρ,hρ,hρs⟩ := exists_pos_lt_subset_ball hS (isClosed_tsupport φ) hs
  let τ := (2*ρ+S)/3
  let R := (ρ+2*S)/3
  have hρτ : ρ<τ := by dsimp only [τ]; linarith [hρ.2]
  have hτR : τ<R := by dsimp only [τ,R]; linarith [hρ.2]
  have hRS : R<S := by dsimp only [R]; linarith [hρ.2]
  refine hX.weighted_mixed_energy_tendsto hn hS (hρ.1.le.trans hρτ.le) hρτ hτR hRS
    p r ε V hr hcurv hε hε1 hεlim hV u q ψ G hψ hG ?_ ?_ hM hQ
    (hub.mono fun _ hk => ae_restrict_of_ae hk) (hqb.mono fun _ hk => ae_restrict_of_ae hk)
    φ hφ ((subset_tsupport φ).trans hρs) ?_ ?_
  · intro W _ hWS δ hδ
    exact (huv δ hδ).mono fun k hk => ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (mul_le_mul_of_nonneg_right hWS.le (hr k).le)) hk
  · intro W _ hWS δ hδ
    exact (hqv δ hδ).mono fun k hk => ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (mul_le_mul_of_nonneg_right hWS.le (hr k).le)) hk
  · intro δ hδ
    exact (huenergy.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hδ))).mono fun _ hk => hk.le
  · intro δ hδ
    exact (hqenergy.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hδ))).mono fun _ hk => hk.le

end RegularPointCoordinates

end

end OAI
