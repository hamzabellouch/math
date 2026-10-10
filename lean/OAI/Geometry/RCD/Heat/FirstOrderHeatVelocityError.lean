import OAI.Geometry.RCD.Harmonic.FirstOrderVelocityErrorLimit
import OAI.Geometry.RCD.Coordinates.FrameVelocityErrorLocality
import OAI.Geometry.RCD.Heat.BoundedHeatFullSource
import OAI.Geometry.RCD.Coordinates.BoundedRegularLocalization
import OAI.Geometry.RCD.Heat.HeatFullMassBound
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent

namespace OAI

/-! # Vanishing spatial velocity error for the actual bounded heat tests -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_heat_velocity_error {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    {η : ℝ} (hη : 0<η) (hη1 : η≤1)
    (h : ℕ → Lp ℝ 2 (hausdorff n X)) (V : ℕ → X → ℝ) (L : ℝ≥0) (A : ℕ → ℝ≥0)
    (hV : ∀ k, LipschitzWith L (V k)) (hVc : ∀ k, HasCompactSupport (V k))
    (hrep : ∀ k, V k =ᵐ[hausdorff n X] h k)
    (hA : ∀ k, ∀ᵐ x ∂hausdorff n X, |h k x|≤A k) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let hs (k : ℕ) : 0<η*(r k)^2 := mul_pos hη (sq_pos_of_pos (hr k))
    let w k := heatSobolev μ Q (η*(r k)^2) (hs k) (h k)
    (∀ k, IntegrableOn (frameVelocityError μ Q (u k) (w k)) (ball (p k) (r k)) μ) ∧
    Tendsto (fun k => (μ.real (ball (p k) (4*r k)))⁻¹*
      ∫ x in ball (p k) (r k), frameVelocityError μ Q (u k) (w k) x ∂μ) atTop (𝓝 0) := by
  intro μ Q hs w
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let hk k := hX.canonicalHeatKernel_isContinuousHeatKernel hn (p k)
  let d k := heatSobolevMap μ Q (η*(r k)^2/2) (half_pos (hs k))
    (-heatGeneratorAt μ Q (η*(r k)^2-η*(r k)^2/2) (h k))
  let b (k : ℕ) : ℝ≥0 := ⟨(2*(n:ℝ)*(|K|+1/(η*(r k)^2)))*(A k:ℝ),by positivity⟩
  have hd (k : ℕ) : IsWeakLaplacian μ Q (w k) (SobolevSpace.toLp μ Q (d k)) :=
    heatTail_weak_laplacian μ Q _ (hs k) (h k)
  have hdb (k : ℕ) : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (d k) x|≤b k := by
    have he : SobolevSpace.toLp μ Q (d k)=-heatGeneratorAt μ Q (η*(r k)^2) (h k) :=
      heatTail_deriv_toLp μ Q _ (half_pos (hs k)) (h k) _ (by linarith [hs k])
    rw [he]
    filter_upwards [hX.heatGeneratorAt_amplitude hn (p k) hK (h k) (A k) (hA k) (hs k),
      Lp.coeFn_neg (heatGeneratorAt μ Q (η*(r k)^2) (h k))] with x hx he
    rw [he]
    change |-heatGeneratorAt μ Q (η*(r k)^2) (h k) x|≤(b k:ℝ)
    simpa only [abs_neg,b] using! hx
  have hlocal (k : ℕ) : ∃ (g : compactLaplacianCore μ Q univ) (q : Lp ℝ 2 μ),
      IsWeakLaplacian μ Q g.val q ∧
      SobolevSpace.toLp μ Q g.val =ᵐ[μ.restrict (ball (p k) (4*r k))] SobolevSpace.toLp μ Q (w k) ∧
      q =ᵐ[μ.restrict (ball (p k) (4*r k))] SobolevSpace.toLp μ Q (d k) := by
    obtain ⟨C,_hC,⟨χ⟩⟩ := hX.goodCutoff_exists hn (p k)
      (r := 4*r k) (mul_pos (by norm_num) (hr k))
    obtain ⟨hLip,_⟩ := hX.kernelHeat_bounded_regularity hn (p k) (hk k) (h k) (A k) (hA k) _ (hs k)
    have hw : SobolevSpace.toLp μ Q (w k) =ᵐ[μ] kernelHeat μ Q (hk k) (η*(r k)^2) (h k) := by
      simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 μ Q (hk k) (hs k) (h k)).symm
    exact bounded_regular_localization μ Q (w k) _ (hd k) _ hLip hw (A k)
      (hX.bounded_heat_sobolev_data hn (p k) (h k) (A k) (hA k) (hs k)).1 χ
  choose g q hq hgw hqd using hlocal
  have hW (k : ℕ) : ∀ᵐ x ∂μ, localGamma μ Q (w k) (w k) x≤((L:ℝ)*Real.exp 1)^2 := by
    have hc : (-K)*(r k)^2≤1 := by
      have hh : K*(16*r k)^2=256*(K*(r k)^2) := by ring
      have hb := hcurv k
      rw [hh] at hb
      nlinarith
    have he : -K*(η*(r k)^2)≤1 := by
      calc
        _=η*((-K)*(r k)^2) := by ring
        _≤η*1 := mul_le_mul_of_nonneg_left hc hη.le
        _≤1 := by simpa only [mul_one] using hη1
    have hl := hX.heat_compact_slope_bdd K n hn (hV k) (hVc k) (p k) (h k) (hrep k) _ (hs k)
    have hb : (L:ℝ)*Real.exp (-K*(η*(r k)^2))≤(L:ℝ)*Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) L.coe_nonneg
    filter_upwards [hl,localGamma_self μ Q (w k),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q (w k))] with x hx he h0
    rw [he]
    exact pow_le_pow_left₀ h0 (hx.trans hb) 2
  have hsub (k : ℕ) : ball (p k) (2*r k)⊆ball (p k) (4*r k) :=
    ball_subset_ball (by linarith [hr k])
  have hg (k : ℕ) : ∀ᵐ x ∂μ.restrict (ball (p k) (2*r k)),
      localGamma μ Q (g k).val (g k).val x≤((L:ℝ)*Real.exp 1)^2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hsub k)
      (localGamma_pair_congr_ae μ Q (hgw k) (hgw k)),ae_restrict_of_ae (hW k)] with x hx hy
    exact hx.trans_le hy
  obtain ⟨hI,hlim⟩ := hX.first_order_velocity_error_tendsto hn hK p r ε hr hcurv hε hε1 hε0
    u v hsplit g q hq d b hdb hqd hg
  have hE (k : ℕ) := ae_restrict_of_ae_restrict_of_subset (hsub k)
    (frameVelocityError_congr_ae μ Q (u k) (hgw k))
  have hIw (k : ℕ) : IntegrableOn (frameVelocityError μ Q (u k) (w k)) (ball (p k) (2*r k)) μ :=
    (hI k).congr (hE k)
  have hlimw : Tendsto (fun k => (μ.real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k), frameVelocityError μ Q (u k) (w k) x ∂μ) atTop (𝓝 0) := by
    convert hlim using 1
    funext k
    rw [integral_congr_ae (hE k)]
  have hrsub (k : ℕ) : ball (p k) (r k)⊆ball (p k) (2*r k) := ball_subset_ball (by linarith [hr k])
  refine ⟨fun k => (hIw k).mono_set (hrsub k),?_⟩
  apply squeeze_zero (fun k => mul_nonneg (by positivity)
    (integral_nonneg (frameVelocityError_nonneg μ Q (u k) (w k)))) ?_ hlimw
  intro k
  have hpos : 0<μ.real (ball (p k) (2*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos (by norm_num) (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hvol : μ.real (ball (p k) (2*r k))≤μ.real (ball (p k) (4*r k)) :=
    measureReal_mono (hsub k) (hX.finiteOnBounded _ isBounded_ball).ne
  exact mul_le_mul (by simpa only [one_div] using one_div_le_one_div_of_le hpos hvol)
    (setIntegral_mono_set (hIw k) (Eventually.of_forall (frameVelocityError_nonneg μ Q (u k) (w k)))
      (Eventually.of_forall (hrsub k))) (integral_nonneg (frameVelocityError_nonneg μ Q (u k) (w k)))
    (by positivity)

end RegularPointCoordinates

end

end OAI
