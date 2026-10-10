import OAI.Geometry.RCD.Sobolev.WeightedBallEnergyLiminf
import OAI.Geometry.RCD.Sobolev.WeightedRecoveryEnergy

namespace OAI

/-! # Exact weighted energies of the actual compact recoveries -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.weighted_recovery_energy_tendsto {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S ρ τ R c : ℝ} (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (hτR : τ<R) (hRS : R<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ)
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-ψ (v k x)|≤δ)
    (hzero : ∀ k, ∀ᵐ x ∂hausdorff n X, x∉ball (p k) (c*r k) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x=0)
    (hgrad : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (c*r k)),
        r k*SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (w k) x≤
          ‖fderiv ℝ ψ (v k x)‖+η)
    (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0≤φ z) (hs : Function.support φ⊆ball 0 ρ) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (S*r k), φ (v k x)*localGamma (hausdorff n X) hX.quadratic
        (w k) (w k) x ∂hausdorff n X)) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
        ∫ z in ball 0 S, φ z*‖fderiv ℝ ψ z‖^2)) := by
  let G := smoothGradientTest (hψ.1.of_le (by simp)) hψ.2.1
  obtain ⟨_,_,_,L,_,hL,_,_⟩ := hψ.metric_bounds hS
  have hbound : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤(‖G‖+1)^2 := by
    filter_upwards [hgrad 1 zero_lt_one] with k hk
    have hfull := supported_recovery_slope (hausdorff n X) hX.quadratic (w k) measurableSet_ball
      (fun x => by positivity) (hzero k) hk
    filter_upwards [ae_restrict_of_ae hfull,
      ae_restrict_of_ae (localGamma_self (hausdorff n X) hX.quadratic (w k)),
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr
        (SobolevSpace.minimalSlope_nonneg (hausdorff n X) hX.quadratic (w k)))] with x hx he hn
    have hb : ‖fderiv ℝ ψ (v k x)‖≤‖G‖ := by
      simpa only [G,smoothGradientTest_apply,Real.norm_eq_abs,abs_norm] using G.norm_coe_le_norm (v k x)
    rw [he,← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (hr k).le hn) (hx.trans (add_le_add hb le_rfl)) 2
  have hlo := hX.weighted_energy_eventual_lower_on_ball hn hS hτ hρτ hτR hRS
    p r ε v hr hcurv hε hε1 hεlim hv w ψ (fun _ _ => ⟨L,hL.lipschitzOnWith⟩)
    hconv φ hφ hs (sq_nonneg (‖G‖+1)) hbound
  have hup := hX.weighted_recovery_energy_upper hS p r ε v hr hεlim hv
    (hψ.1.of_le (by simp)) hψ.2.1 φ hφ w hzero hgrad
  have heq : (∫ z, φ z*‖fderiv ℝ ψ z‖^2)=∫ z in ball (0:Euclidean n) S, φ z*‖fderiv ℝ ψ z‖^2 := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzφ : φ z=0 := Function.notMem_support.mp (fun hh =>
      hz ((ball_subset_ball (hρτ.trans (hτR.trans hRS)).le) (hs hh)))
    rw [hzφ,zero_mul]
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [hlo (δ/2) (half_pos hδ),hup (δ/2) (half_pos hδ)] with k hklo hkup
  simp only [heq,div_eq_mul_inv] at hklo
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end RegularPointCoordinates

end

end OAI
