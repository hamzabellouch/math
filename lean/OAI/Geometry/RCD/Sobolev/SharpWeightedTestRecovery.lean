import OAI.Geometry.RCD.Sobolev.WeightedRecoveryConvergence

namespace OAI

/-! # Actual Dirichlet tests with exact compactly weighted energies

One recovered sequence works for every nonnegative compact interior weight.
The sequence is the original Hopf--Lax recovery, with no energy convergence
assumed of it.
-/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.sharp_weighted_test_recovery {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {S : ℝ} (hS : 0<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ) :
    ∃ c : ℝ, 0<c ∧ c<S ∧ ∃ N : ℕ, ∃ q : ∀ k : ℕ,
      SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball (p (k+N)) (S*r (k+N))),
      (∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+N)) (S*r (k+N))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k).val x-ψ (v (k+N) x)|≤δ) ∧
      (∀ ρ : ℝ, 0≤ρ → ρ<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+N)) (ρ*r (k+N))),
          r (k+N)*SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (q k).val x≤
            ‖fderiv ℝ ψ (v (k+N) x)‖+δ) ∧
      (∀ k, ∀ᵐ x ∂hausdorff n X, x∉ball (p (k+N)) (c*r (k+N)) →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k).val x=0) ∧
      ∀ φ : Euclidean n →ᵇ ℝ, (∀ z, 0≤φ z) → tsupport φ⊆ball 0 S →
        Tendsto (fun k => r (k+N)^2*((hausdorff n X).real (ball (p (k+N)) (S*r (k+N))))⁻¹*
          ∫ x in ball (p (k+N)) (S*r (k+N)), φ (v (k+N) x)*localGamma (hausdorff n X) hX.quadratic
            (q k).val (q k).val x ∂hausdorff n X) atTop
          (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
            ∫ z in ball 0 S, φ z*‖fderiv ℝ ψ z‖^2)) := by
  obtain ⟨c,hc,hcS,N,q,hq,hg,hz⟩ :=
    hX.sharp_test_recovery_sequence_supported hS p r ε v hr hε hεlim hv hψ
  refine ⟨c,hc,hcS,N,q,hq,hg,hz,?_⟩
  intro φ hφ hs
  obtain ⟨ρ,hρ,hsub⟩ := exists_pos_lt_subset_ball hS (isClosed_tsupport φ) hs
  let τ := (2*ρ+S)/3
  let R := (ρ+2*S)/3
  have hρτ : ρ<τ := by dsimp only [τ]; linarith [hρ.2]
  have hτR : τ<R := by dsimp only [τ,R]; linarith [hρ.2]
  have hRS : R<S := by dsimp only [R]; linarith [hρ.2]
  apply hX.weighted_recovery_energy_tendsto hn hS (hρ.1.le.trans hρτ.le) hρτ hτR hRS
    (fun k => p (k+N)) (fun k => r (k+N)) (fun k => ε (k+N)) (fun k => v (k+N))
    (fun k => hr (k+N)) (fun k => hcurv (k+N))
    (fun k => hε (k+N)) (fun k => hε1 (k+N)) (hεlim.comp (tendsto_add_atTop_nat N))
    (fun k => hv (k+N)) (fun k => (q k).val) hψ _ hz (hg c hc.le hcS) φ hφ
    ((subset_tsupport φ).trans hsub)
  intro W hW hWS δ hδ
  filter_upwards [hq δ hδ] with k hk
  exact ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (mul_le_mul_of_nonneg_right hWS.le (hr (k+N)).le)) hk

end RegularPointCoordinates

end

end OAI
