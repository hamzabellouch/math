import OAI.Geometry.RCD.Coordinates.FrameVelocityErrorLimit
import OAI.Geometry.RCD.Coordinates.FirstOrderFrameErrorIntegral
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Vanishing actual velocity error on the original radius-two balls -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_velocity_error_tendsto {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hs : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (g : ℕ → compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (q : ℕ → Lp ℝ 2 (hausdorff n X))
    (hq : ∀ k, IsWeakLaplacian (hausdorff n X) hX.quadratic (g k).val (q k))
    (d : ℕ → SobolevSpace (hausdorff n X) hX.quadratic) (A : ℕ → ℝ≥0)
    (hd : ∀ k, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (d k) x|≤A k)
    (hqr : ∀ k, q k =ᵐ[(hausdorff n X).restrict (ball (p k) (4*r k))]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (d k))
    {L : ℝ} (hg : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (2*r k)),
      localGamma (hausdorff n X) hX.quadratic (g k).val (g k).val x≤L^2) :
    (∀ k, IntegrableOn (frameVelocityError (hausdorff n X) hX.quadratic (u k) (g k).val)
      (ball (p k) (2*r k)) (hausdorff n X)) ∧
    Tendsto (fun k => ((hausdorff n X).real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k), frameVelocityError (hausdorff n X) hX.quadratic (u k) (g k).val x
        ∂hausdorff n X) atTop (𝓝 0) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  have hpos (k : ℕ) (a : ℝ) (ha : 0<a) : 0<μ.real (ball (p k) (a*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos ha (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)<1/8) (by norm_num : (1/8:ℝ)≤1)
  have hv (k : ℕ) : μ.real (ball (p k) (16*r k))≤D*μ.real (ball (p k) (2*r k)) := by
    have hh := hvol (p k) (16*r k) (mul_pos (by norm_num) (hr k)) (hcurv k) (p k)
      (by simpa only [dist_self] using mul_nonneg (by norm_num : (0:ℝ)≤16) (hr k).le)
    simpa only [show (1/8:ℝ)*(16*r k)=2*r k by ring] using hh
  have hC : 0≤frameDefectConstant n := by unfold frameDefectConstant; positivity
  have hEsq (k : ℕ) := hX.first_order_frame_error_integral hn hK (p k)
    (mul_pos (by norm_num) (hr k)) (by linarith [hr k]) (hε k) (hε1 k)
    (u k) (v k) (hs k) (g k) (q k) (hq k) (d k) (A k) (hd k)
    (by simpa only [show (2:ℝ)*(2*r k)=4*r k by ring] using hqr k) (hg k)
  have hEbound (k : ℕ) : (μ.real (ball (p k) (2*r k)))⁻¹*
      (∫ x in ball (p k) (2*r k), (frameEnergyError μ Q (u k) (g k).val x)^2 ∂μ)≤
        (frameDefectConstant n*L^4*(n:ℝ)^2*D)*ε k := by
    rw [← div_eq_inv_mul,div_le_iff₀ (hpos k 2 (by norm_num))]
    have hh := mul_le_mul_of_nonneg_left (hv k)
      (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity : 0≤L^4)) (sq_nonneg (n:ℝ))) (hε k))
    exact (hEsq k).2.trans (by
      convert hh using 1
      ring)
  have hDint (k : ℕ) : (∫ x in ball (p k) (2*r k), gramDefect μ Q (u k) x ∂μ)≤
      (n:ℝ)^2*ε k*μ.real (ball (p k) (16*r k)) := by
    have hsub : ball (p k) (2*r k)⊆ball (p k) (16*r k) :=
      ball_subset_ball (by linarith [hr k])
    have hi : IntegrableOn (gramDefect μ Q (u k)) (ball (p k) (16*r k)) μ :=
      gramDefect_integrableOn μ Q (u k) (hX.finiteOnBounded _ isBounded_ball).ne
    exact (setIntegral_mono_set hi (Eventually.of_forall (fun x => gramDefect_nonneg μ Q (u k) x))
      (Eventually.of_forall hsub)).trans (gramDefect_integral_bound μ Q (hpos k 16 (by norm_num))
        (hX.finiteOnBounded _ isBounded_ball).ne (hs k))
  have hDbound (k : ℕ) : (μ.real (ball (p k) (2*r k)))⁻¹*
      (∫ x in ball (p k) (2*r k), gramDefect μ Q (u k) x ∂μ)≤((n:ℝ)^2*D)*ε k := by
    rw [← div_eq_inv_mul,div_le_iff₀ (hpos k 2 (by norm_num))]
    have hh := mul_le_mul_of_nonneg_left (hv k) (mul_nonneg (sq_nonneg (n:ℝ)) (hε k))
    exact (hDint k).trans (by
      convert hh using 1
      ring)
  have hEzero : Tendsto (fun k => (μ.real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k), (frameEnergyError μ Q (u k) (g k).val x)^2 ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => mul_nonneg (inv_nonneg.mpr (hpos k 2 (by norm_num)).le)
      (integral_nonneg (fun _ => sq_nonneg _))) hEbound
    simpa only [mul_zero] using hε0.const_mul (frameDefectConstant n*L^4*(n:ℝ)^2*D)
  have hDzero : Tendsto (fun k => (μ.real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k), gramDefect μ Q (u k) x ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => mul_nonneg (inv_nonneg.mpr (hpos k 2 (by norm_num)).le)
      (integral_nonneg (gramDefect_nonneg μ Q (u k)))) hDbound
    simpa only [mul_zero] using hε0.const_mul ((n:ℝ)^2*D)
  apply frame_velocity_error_tendsto μ Q u (fun k => (g k).val) (fun k => ball (p k) (2*r k))
    (fun _ => (hX.finiteOnBounded _ isBounded_ball).ne) (fun k => hpos k 2 (by norm_num))
    ?_ hg (fun k => (hEsq k).1) hEzero hDzero
  intro k i
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith [hr k]))
    ((hs k).gradient i)] with x hx
  nlinarith [hε k,hε1 k]

end RegularPointCoordinates

end

end OAI
