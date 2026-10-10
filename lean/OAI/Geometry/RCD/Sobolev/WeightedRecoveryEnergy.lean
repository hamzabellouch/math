import OAI.Geometry.RCD.Metric.WeightedRecoveryError
import OAI.Geometry.RCD.Sobolev.SharpTestRecoverySequence
import OAI.Geometry.RCD.Sobolev.SmoothGradientTest
import OAI.Geometry.RCD.Metric.SupportedRecoverySlope

namespace OAI

/-! # Sharp compactly weighted energy upper bounds

The fixed interior support extends the local slope estimate to the whole
physical ball. Measured convergence then gives the Euclidean Dirichlet energy
with no multiplicative loss.
-/

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.weighted_recovery_energy_upper {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S c : ℝ} (hS : 0<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    {ψ : Euclidean n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ)
    (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0≤φ z)
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hzero : ∀ k, ∀ᵐ x ∂hausdorff n X, x∉ball (p k) (c*r k) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x=0)
    (hgrad : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (c*r k)),
        r k*SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (w k) x≤
          ‖fderiv ℝ ψ (v k x)‖+η) :
    ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
        (∫ x in ball (p k) (S*r k), φ (v k x)*localGamma (hausdorff n X) hX.quadratic
          (w k) (w k) x ∂hausdorff n X)≤
      (volume.real (ball (0:Euclidean n) S))⁻¹*
        (∫ z in ball 0 S, φ z*‖fderiv ℝ ψ z‖^2)+δ := by
  let μ := hausdorff n X
  let G := smoothGradientTest hψ hs
  have hfin (k : ℕ) : μ (ball (p k) (S*r k))≠⊤ :=
    (hX.finiteOnBounded _ isBounded_ball).ne
  let : ∀ k, IsFiniteMeasure (μ.restrict (ball (p k) (S*r k))) := fun k =>
    ⟨by simpa only [Measure.restrict_apply_univ] using (hfin k).lt_top⟩
  have hmass (k : ℕ) : 0<μ.real (ball (p k) (S*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne' (hfin k)
  have hlim := physical_ball_measured_test_tendsto hS hS le_rfl hr hv hfin hmass hε (φ*G^2)
  change Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹*
    ∫ x in ball (p k) (S*r k), φ (v k x)*(G (v k x))^2 ∂μ) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
        ∫ z in ball 0 S, φ z*(G z)^2)) at hlim
  intro δ hδ
  let η := min 1 (δ/(2*(‖φ‖+1)*(2*‖G‖+1)))
  have hden : 0<2*(‖φ‖+1)*(2*‖G‖+1) := by positivity
  have hη : 0<η := lt_min zero_lt_one (div_pos hδ hden)
  have hη1 : η≤1 := min_le_left _ _
  have hηδ : ‖φ‖*η*(2*‖G‖+η)≤δ/2 := by
    have hh := (le_div_iff₀ hden).mp
      (min_le_right 1 (δ/(2*(‖φ‖+1)*(2*‖G‖+1))))
    have h1 := mul_le_mul_of_nonneg_left
      (add_le_add_left hη1 (2*‖G‖)) (mul_nonneg (norm_nonneg φ) hη.le)
    have h2 := mul_le_mul_of_nonneg_right (show ‖φ‖≤‖φ‖+1 by linarith)
      (mul_nonneg hη.le (show 0≤2*‖G‖+1 by positivity))
    dsimp only [η] at h1 h2 ⊢
    nlinarith only [hh,h1,h2]
  have hev := hlim.eventually (Iio_mem_nhds (show
      (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z in ball 0 S, φ z*(G z)^2)<
      (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z in ball 0 S, φ z*(G z)^2)+δ/2 by linarith))
  filter_upwards [hgrad η hη,hev] with k hk he
  have hfull := supported_recovery_slope μ hX.quadratic (w k) measurableSet_ball
    (fun x => add_nonneg (norm_nonneg _) hη.le) (hzero k) hk
  have hGm : AEStronglyMeasurable (fun x => G (v k x)) (μ.restrict (ball (p k) (S*r k))) :=
    (G.continuous.measurable.comp (hv k).measurable).aestronglyMeasurable
  have hGb : ∀ᵐ x ∂μ.restrict (ball (p k) (S*r k)), 0≤G (v k x) ∧ G (v k x)≤‖G‖ :=
    Eventually.of_forall fun x => ⟨by simp only [G,smoothGradientTest_apply]; positivity,
      le_trans (le_abs_self _) (G.norm_coe_le_norm _)⟩
  have hφm : AEStronglyMeasurable (fun x => φ (v k x)) (μ.restrict (ball (p k) (S*r k))) :=
    (φ.continuous.measurable.comp (hv k).measurable).aestronglyMeasurable
  have hφb : ∀ᵐ x ∂μ.restrict (ball (p k) (S*r k)), 0≤φ (v k x) ∧ φ (v k x)≤‖φ‖ :=
    Eventually.of_forall fun x => ⟨hφ _, (le_abs_self _).trans (φ.norm_coe_le_norm _)⟩
  have hb := weighted_recovery_energy_error μ hX.quadratic (hmass k) (hr k).le (w k)
    (norm_nonneg G) hη.le hGm hφm hGb hφb (ae_restrict_of_ae hfull)
  have ht := hb.trans (add_le_add he.le hηδ)
  simpa only [G,smoothGradientTest_apply,add_assoc,add_halves] using ht

end RegularPointCoordinates

end

end OAI
