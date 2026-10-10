import OAI.Geometry.RCD.Coordinates.HeatFrameUniformEnergy
import OAI.Geometry.RCD.Coordinates.FirstOrderRegularFamily
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Uniform actual heat-frame energy along the original splitting sequence -/

open Set Filter MeasureTheory Metric Finset
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_heat_frame_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hcurv : ∀ k, -1≤K*(16*r k)^2) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    {η : ℝ} (hη : 0<η) (hη1 : η≤1)
    (h : ℕ → Lp ℝ 2 (hausdorff n X)) (V : ℕ → X → ℝ) (L a : ℝ≥0) (A : ℕ → ℝ≥0)
    (hV : ∀ k, LipschitzWith L (V k)) (hVc : ∀ k, HasCompactSupport (V k))
    (hrep : ∀ k, V k =ᵐ[hausdorff n X] h k)
    (hA : ∀ k, ∀ᵐ x ∂hausdorff n X, |h k x|≤A k) (hscale : ∀ k, (A k:ℝ)≤a*r k) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let hs (k : ℕ) : 0<η*(r k)^2 := mul_pos hη (sq_pos_of_pos (hr k))
    let w k := heatSobolev μ Q (η*(r k)^2) (hs k) (h k)
    ∃ (M : ℝ) (G : ℕ → Fin n → SobolevSpace μ Q), 0<M ∧
      (∀ k i, SobolevSpace.toLp μ Q (G k i) =ᵐ[μ.restrict (ball (p k) (4*r k))]
        localGamma μ Q (u k i) (w k)) ∧
      ∀ k, (r k)^2*(∑ i, ∫ x in ball (p k) (r k), localGamma μ Q (G k i) (G k i) x ∂μ)≤
        M*μ.real (ball (p k) (4*r k)) := by
  intro μ Q hs w
  classical
  choose U q W LU AU hq hW hWc hUr hAU hsame hq0 hWeq hgrad using fun k =>
    hX.first_order_regular_family hn (hr k) (hε k) (hε1 k) (u k) (v k) (hsplit k)
  have hsmall (k : ℕ) : (-K)*(r k)^2≤1 := by
    nlinarith [hcurv k,mul_nonneg (neg_nonneg.mpr hK) (sq_nonneg (r k))]
  obtain ⟨C,hC,hcut⟩ := hX.goodCutoffInput hn
  have hC0 : 0≤C := by linarith
  let χ k := Classical.choice (hcut (p k) (r k) (hr k) (by nlinarith [hsmall k]))
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)≤1)
  have hD0 : 0≤D := by linarith
  have hm (k : ℕ) (c : ℝ) (hc : 0<c) : 0<μ.real (ball (p k) (c*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hc (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hv (k : ℕ) : μ.real (ball (p k) (16*r k))≤D*μ.real (ball (p k) (4*r k)) := by
    have hh := hvol (p k) (16*r k) (by linarith [hr k]) (hcurv k) (p k)
      (by simpa only [dist_self] using mul_nonneg (by norm_num : (0:ℝ)≤16) (hr k).le)
    simpa only [show (1/4:ℝ)*(16*r k)=4*r k by ring] using hh
  have he (k : ℕ) (i : Fin n) :
      (∫ x in closedBall (p k) (2*r k), |localGamma μ Q (U k i).val (U k i).val x-1| ∂μ)≤
        D*μ.real (ball (p k) (4*r k)) := by
    let : IsFiniteMeasure (μ.restrict (ball (p k) (16*r k))) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded _ isBounded_ball⟩
    have hi : IntegrableOn (fun x => |localGamma μ Q (u k i) (u k i) x-1|)
        (ball (p k) (16*r k)) μ :=
      ((localGamma_memL1 μ Q (u k i) (u k i)).integrableOn.sub (integrable_const _)).abs
    have hloc : localGamma μ Q (U k i).val (U k i).val
        =ᵐ[μ.restrict (closedBall (p k) (2*r k))] localGamma μ Q (u k i) (u k i) :=
      ae_restrict_of_ae_restrict_of_subset (closedBall_subset_ball (by linarith [hr k]))
        (localGamma_pair_congr_ae μ Q (hsame k i) (hsame k i))
    have hEq := integral_congr_ae (hloc.fun_comp (fun z : ℝ => |z-1|))
    simp only [Function.comp_apply] at hEq
    rw [hEq]
    apply (setIntegral_mono_set hi (Eventually.of_forall (fun _ => abs_nonneg _))
      (Eventually.of_forall (closedBall_subset_ball (by linarith [hr k])))).trans
    have hmean := (hsplit k).gram i i
    rw [← div_eq_inv_mul,div_le_iff₀ (hm k 16 (by norm_num))] at hmean
    have hb : (∫ x in ball (p k) (16*r k), |localGamma μ Q (u k i) (u k i) x-1| ∂μ)≤
        ε k*μ.real (ball (p k) (16*r k)) := by simpa only [ite_true] using hmean
    exact (hb.trans (mul_le_of_le_one_left (hm k 16 (by norm_num)).le (hε1 k))).trans (hv k)
  let H := (L:ℝ)*Real.exp 1
  let B := 2*(n:ℝ)*(1+1/η)*(a:ℝ)
  let N := 2*H^2*((C/2+1)*D+1)+8*((C/2+1)*H^2+B^2+B*H*C)
  have hN : 0≤N := by dsimp only [N,H,B]; positivity
  have hfamily (k : ℕ) : ∃ G : Fin n → SobolevSpace μ Q,
      (∀ i, SobolevSpace.toLp μ Q (G i) =ᵐ[μ.restrict (ball (p k) (4*r k))]
        localGamma μ Q (U k i).val (w k)) ∧
      ∀ i, (r k)^2*(∫ x in ball (p k) (r k), localGamma μ Q (G i) (G i) x ∂μ)≤
        N*μ.real (ball (p k) (4*r k)) := by
    apply hX.heat_frame_uniform_energy hn hK (p k) (hr k) hη hη1 (by linarith) (hsmall k) (χ k)
      (U k) (q k) (hq k) _ _ (he k) (h k) (V k) L (A k) a (hV k) (hVc k) (hrep k) (hA k) (hscale k)
    · intro i
      exact ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith [hr k])) (hq0 k i)
    · intro i
      exact ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith [hr k])) (hgrad k i)
  choose G hG hGE using hfamily
  refine ⟨(n:ℝ)*N+1,G,by positivity,?_,?_⟩
  · intro k i
    have hloc := localGamma_pair_congr_ae μ Q
      (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith [hr k])) (hsame k i))
      (EventuallyEq.refl _ _ : SobolevSpace.toLp μ Q (w k) =ᵐ[μ.restrict (ball (p k) (4*r k))]
        SobolevSpace.toLp μ Q (w k))
    exact (hG k i).trans hloc
  · intro k
    have hh := sum_le_sum (fun i (_ : i∈(univ : Finset (Fin n))) => hGE k i)
    rw [← mul_sum] at hh
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    exact hh.trans (by nlinarith [(hm k 4 (by norm_num)).le])

end RegularPointCoordinates

end

end OAI
