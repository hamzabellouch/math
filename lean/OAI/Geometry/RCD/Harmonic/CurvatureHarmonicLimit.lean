import OAI.Geometry.RCD.Harmonic.CurvatureHarmonicVariation
import OAI.Geometry.RCD.Sobolev.CompactEnergyHarmonic
import OAI.Geometry.RCD.Sobolev.SharpRecoveryEnergy
import OAI.Geometry.RCD.Sobolev.HarmonicScaledEnergy
import OAI.Geometry.RCD.Coordinates.EuclideanWeakHarmonicRegularity

namespace OAI

/-! # The weak Euclidean equation under the original curvature-scale bound

Sharp recovered test energies and harmonic orthogonality force the compact
Euclidean gradient pairing to vanish. No energy convergence is assumed.
-/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_value_limit_weak_of_curvature {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S : ℝ} (hS : 0<S) (p : ℕ → X) (r ε : ℕ → ℝ)
    (hr : ∀ k, 0<r k)
    (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (v : ℕ → X → Euclidean n) (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤1)
    (g : Euclidean n → ℝ)
    (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤δ) :
    EuclideanWeakHarmonicOn g S := by
  intro ψ hψ
  obtain ⟨a,ha,hs⟩ := exists_pos_lt_subset_ball hS (isClosed_tsupport ψ) hψ.2.2
  obtain ⟨c,hc,hcS,N,q,hqc,hqg,hqz⟩ :=
    hX.sharp_test_recovery_sequence_supported hS p r ε v hr hε hεlim hv hψ
  let ρ := (max a c+S)/2
  let τ := (ρ+S)/2
  let R := (τ+S)/2
  have hmax : max a c<S := max_lt ha.2 hcS
  have hρ : 0<ρ := by dsimp only [ρ]; linarith [le_max_left a c,ha.1]
  have haρ : a<ρ := by dsimp only [ρ]; linarith [le_max_left a c]
  have hcρ : c<ρ := by dsimp only [ρ]; linarith [le_max_right a c]
  have hρS : ρ<S := by dsimp only [ρ]; linarith
  have hρτ : ρ<τ := by dsimp only [τ]; linarith
  have hτR : τ<R := by dsimp only [R,τ]; linarith
  have hRS : R<S := by dsimp only [R,τ]; linarith
  have hτ : 0≤τ := hρ.le.trans hρτ.le
  have hcR : c<R := hcρ.trans (hρτ.trans hτR)
  obtain ⟨M,hM,hwb⟩ := hX.harmonic_scaled_energy_bound hn hS
    (hτ.trans hτR.le) hRS (fun k => p (k+N)) (fun k => r (k+N))
    (fun k => hr (k+N)) (fun k => hcurv (k+N)) (fun k => w (k+N))
    (fun k => hw (k+N)) (fun k => hnorm (k+N))
  obtain ⟨_,_,_,L,_,hL,_,_⟩ := hψ.metric_bounds hS
  let G := smoothGradientTest (hψ.1.of_le (by simp)) hψ.2.1
  have hqb : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r (k+N)^2*localGamma (hausdorff n X) hX.quadratic (q k).val (q k).val x≤(‖G‖+1)^2 := by
    filter_upwards [hqg c hc.le hcS 1 zero_lt_one] with k hk
    have hfull := supported_recovery_slope (hausdorff n X) hX.quadratic (q k).val
      measurableSet_ball (fun x => add_nonneg (norm_nonneg _) zero_le_one) (hqz k) hk
    filter_upwards [hfull,localGamma_self (hausdorff n X) hX.quadratic (q k).val,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg (hausdorff n X) hX.quadratic (q k).val)]
      with x hx he hn'
    have hb : ‖fderiv ℝ ψ (v (k+N) x)‖≤‖G‖ := by
      simpa only [G,smoothGradientTest_apply,abs_of_nonneg (norm_nonneg _)] using
        (le_abs_self (G (v (k+N) x))).trans (G.norm_coe_le_norm _)
    rw [he]
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg (hr (k+N)).le hn')
      (hx.trans (add_le_add hb le_rfl)) 2
  have hqupper := hX.recovery_energy_upper hS (fun k => p (k+N))
    (fun k => r (k+N)) (fun k => ε (k+N)) (fun k => v (k+N))
    (fun k => hr (k+N)) (hεlim.comp (tendsto_add_atTop_nat N))
    (fun k => hv (k+N)) (hψ.1.of_le (by simp)) hψ.2.1 (fun k => (q k).val)
    hqz (hqg c hc.le hcS)
  apply compact_energy_variation_harmonic hS hρS hg hψ
    (hs.trans (ball_subset_ball haρ.le)) (M := volume.real (ball (0:Euclidean n) S)*M)
  intro t
  have hvar := hX.curvature_harmonic_variation hn hS hτ hρτ hτR hRS hcR
    (fun k => p (k+N)) (fun k => r (k+N)) (fun k => ε (k+N)) (fun k => v (k+N))
    (fun k => hr (k+N)) (fun k => hcurv (k+N))
    (fun k => hε (k+N)) (fun k => hε1 (k+N)) (hεlim.comp (tendsto_add_atTop_nat N))
    (fun k => hv (k+N)) (fun k => w (k+N)) (fun k => hw (k+N)) g ψ hg hL
    (fun W hW hWS δ hδ => (tendsto_add_atTop_nat N).eventually (hconv W hW hWS δ hδ))
    q hqc hqz hM (sq_nonneg (‖G‖+1)) hwb hqb
    (by simpa only [div_eq_mul_inv] using hqupper) t
  have hV : volume.real (ball (0:Euclidean n) S)≠0 :=
    (ENNReal.toReal_pos (measure_ball_pos volume (0:Euclidean n) hS).ne' measure_ball_ne_top).ne'
  convert hvar using 1
  field_simp

end RegularPointCoordinates

end

end OAI
