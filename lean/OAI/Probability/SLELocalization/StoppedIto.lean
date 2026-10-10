import Mathlib
import OAI.Probability.SLELocalization.StoppedMeshes
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Brownian Stopped estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.BrownianStopped
open BrownianPredictable PredictableLimit BrownianIto TaylorMeshes BrownianField

theorem stopped_fieldSum_tendsto_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (τ : Ω → ℝ) (F V : Ω → ℝ → ℝ → ℝ)
    (hτ : ∀ᵐ ω ∂P, 0 ≤ τ ω ∧ τ ω ≤ T)
    (hreg : ∀ᵐ ω ∂P, FieldRegular (F ω) (V ω) (fun t => B t.toNNReal ω) (τ ω))
    (C : ℕ → ℕ → Ω → ℝ)
    (hCeq : ∀ n i, C n i =ᵐ[P] stoppedCoeff 2 B T τ F n i)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hbound : ∀ n i, ∀ᵐ ω ∂P, |stoppedCoeff 2 B T τ F n i ω| ≤ K₂)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hAbound : ∀ n i, ∀ᵐ ω ∂P, |stoppedCoeff 1 B T τ F n i ω| ≤ K₁) :
    ∀ᵐ ω ∂P, Tendsto (fun n => dyadicDriverSum B T (stoppedCoeff 1 B T τ F) n ω) atTop
      (𝓝 (F ω (τ ω) (B (τ ω).toNNReal ω) - F ω 0 (B 0 ω) -
        (∫ t in (0 : ℝ)..(τ ω), V ω t (B t.toNNReal ω)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω),
          iteratedDeriv 2 (F ω t) (B t.toNNReal ω))) := by
  have he := brownian_dyadic_weighted_quadraticError_tendsto hB T
    C hC hC2 K₂ hK₂ (fun n i => by
      filter_upwards [hCeq n i, hbound n i] with ω he hb
      simpa only [he] using hb)
  have hCeq_all : ∀ᵐ ω ∂P, ∀ n i, C n i ω = stoppedCoeff 2 B T τ F n i ω :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hCeq n))
  have hC_all : ∀ᵐ ω ∂P, ∀ n i, |stoppedCoeff 2 B T τ F n i ω| ≤ K₂ :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hbound n))
  have hA_all : ∀ᵐ ω ∂P, ∀ n i, |stoppedCoeff 1 B T τ F n i ω| ≤ K₁ :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hAbound n))
  filter_upwards [hB.cont, quadraticSum_tendsto hB T, he, hreg, hτ, hC_all, hA_all, hCeq_all]
    with ω hb hQ hE hr hτω hCω hAω hCeqω
  have hEs : Tendsto (fun n => dyadicQuadraticError B T (stoppedCoeff 2 B T τ F) n ω) atTop (𝓝 0) := by
    convert hE using 1
    funext n
    unfold dyadicQuadraticError
    simp only [hCeqω]
  let b : ℝ → ℝ := fun t => B t.toNNReal ω
  have hbc : Continuous b := hb.comp continuous_real_toNNReal
  have hQ' : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1))-b (mesh T n i))^2) atTop (𝓝 (T : ℝ)) := by
    simpa only [quadraticSum, b, mesh_toNNReal] using hQ
  have hE' : Tendsto (fun n => ∑ i ∈ Finset.range (2^n), if mesh T n i < τ ω then
      iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
        ((b (mesh T n (i+1))-b (mesh T n i))^2 - (T : ℝ)/(2 : ℝ)^n) else 0)
        atTop (𝓝 0) := by
    have heq (n : ℕ) : dyadicQuadraticError B T (stoppedCoeff 2 B T τ F) n ω =
        ∑ i ∈ Finset.range (2^n), if mesh T n i < τ ω then
          iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
            ((b (mesh T n (i+1))-b (mesh T n i))^2 - (T : ℝ)/(2 : ℝ)^n) else 0 := by
      unfold dyadicQuadraticError
      apply Finset.sum_congr rfl
      intro i hi
      simp only [stoppedCoeff, b, mesh_toNNReal]
      split_ifs <;> simp
    simpa only [heq] using hEs
  have hA' (n i : ℕ) (hi : mesh T n i < τ ω) :
      |deriv (F ω (mesh T n i)) (b (mesh T n i))| ≤ K₁ := by
    simpa only [stoppedCoeff, ite_eq_left hi, iteratedDeriv_succ, iteratedDeriv_zero,
      b, mesh_toNNReal] using hAω n i
  have hC' (n i : ℕ) (hi : mesh T n i < τ ω) :
      |iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i))| ≤ K₂ := by
    simpa only [stoppedCoeff, ite_eq_left hi, b, mesh_toNNReal] using hCω n i
  have ht := stopped_field_taylor_limit T.coe_nonneg hτω.1 hτω.2 hbc.continuousOn
    hr hQ' hK₁ hK₂ hA' hC' hE'
  have heq (n : ℕ) : dyadicDriverSum B T (stoppedCoeff 1 B T τ F) n ω =
      ∑ i ∈ Finset.range (2^n), if mesh T n i < τ ω then
        deriv (F ω (mesh T n i)) (b (mesh T n i)) *
          (b (mesh T n (i+1))-b (mesh T n i)) else 0 := by
    unfold dyadicDriverSum
    apply Finset.sum_congr rfl
    intro i hi
    simp only [stoppedCoeff, b, mesh_toNNReal, iteratedDeriv_succ, iteratedDeriv_zero]
    split_ifs <;> simp
  simpa only [← heq, b, Real.toNNReal_zero] using ht

theorem stopped_field_ito_centered_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (τ : Ω → ℝ) (F V : Ω → ℝ → ℝ → ℝ)
    (hτ : ∀ᵐ ω ∂P, 0 ≤ τ ω ∧ τ ω ≤ T)
    (hreg : ∀ᵐ ω ∂P, FieldRegular (F ω) (V ω) (fun t => B t.toNNReal ω) (τ ω))
    (A C : ℕ → ℕ → Ω → ℝ)
    (hAeq : ∀ n i, A n i =ᵐ[P] stoppedCoeff 1 B T τ F n i)
    (hCeq : ∀ n i, C n i =ᵐ[P] stoppedCoeff 2 B T τ F n i)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hbound : ∀ n i, ∀ᵐ ω ∂P, |stoppedCoeff 2 B T τ F n i ω| ≤ K₂)
    (hA : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (A n i))
    (hA2 : ∀ n i, MemLp (A n i) 2 P)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hAbound : ∀ n i, ∀ᵐ ω ∂P, |stoppedCoeff 1 B T τ F n i ω| ≤ K₁) :
    let Y := fun ω => F ω (τ ω) (B (τ ω).toNNReal ω) - F ω 0 (B 0 ω) -
      (∫ t in (0 : ℝ)..(τ ω), V ω t (B t.toNNReal ω)) -
      (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω), iteratedDeriv 2 (F ω t) (B t.toNNReal ω)
    Integrable Y P ∧ (∫ ω, Y ω ∂P) = 0 := by
  have ht := stopped_fieldSum_tendsto_ae hB T τ F V hτ hreg C hCeq hC hC2
    K₂ hK₂ hbound K₁ hK₁ hAbound
  have hAeq_all : ∀ᵐ ω ∂P, ∀ n i, A n i ω = stoppedCoeff 1 B T τ F n i ω :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hAeq n))
  apply limit_centered hB T A hA hA2 K₁ hK₁ ?_ _ ?_
  · intro n i
    filter_upwards [hAeq n i, hAbound n i] with ω he hb
    simpa only [he] using hb
  · filter_upwards [ht, hAeq_all] with ω hω he
    convert hω using 1
    funext n
    unfold dyadicDriverSum
    simp only [he]

end SLEExactGauge.BrownianStopped

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.LoewnerCutoff

def clampIm (ε : ℝ) (w : ℂ) : ℂ := ⟨w.re, max w.im ε⟩

def velocity (ε u : ℝ) (w : ℂ) : ℂ := 2 / clampIm ε (w - (u : ℂ))

lemma clampIm_eq {ε : ℝ} {w : ℂ} (hw : ε ≤ w.im) : clampIm ε w = w := by
  apply Complex.ext <;> simp [clampIm, max_eq_left hw]

lemma clampIm_height (ε : ℝ) (w : ℂ) : ε ≤ (clampIm ε w).im := le_max_right _ _

lemma clampIm_norm {ε : ℝ} (_hε : 0 < ε) (w : ℂ) : ε ≤ ‖clampIm ε w‖ :=
  (clampIm_height ε w).trans (Complex.im_le_norm _)

lemma clampIm_ne_zero {ε : ℝ} (hε : 0 < ε) (w : ℂ) : clampIm ε w ≠ 0 :=
  norm_pos_iff.1 (hε.trans_le (clampIm_norm hε w))

lemma clampIm_norm_sub (ε : ℝ) (z w : ℂ) :
    ‖clampIm ε z - clampIm ε w‖ ≤ 2 * ‖z - w‖ := by
  have hm : |max z.im ε - max w.im ε| ≤ |z.im - w.im| := by
    simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (z.im - w.im))] using
      abs_max_sub_max_le_max z.im ε w.im ε
  calc
    ‖clampIm ε z - clampIm ε w‖ ≤ |z.re-w.re| + |max z.im ε-max w.im ε| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |z.re-w.re| + |z.im-w.im| := add_le_add le_rfl hm
    _ ≤ ‖z-w‖ + ‖z-w‖ := add_le_add (Complex.abs_re_le_norm (z-w))
      (Complex.abs_im_le_norm (z-w))
    _ = 2 * ‖z-w‖ := by ring

lemma velocity_eq {ε u : ℝ} {w : ℂ} (hw : ε ≤ w.im) :
    velocity ε u w = 2 / (w - (u : ℂ)) := by
  unfold velocity
  rw [clampIm_eq (by simpa using hw)]

lemma norm_velocity_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) (w : ℂ) :
    ‖velocity ε u w‖ ≤ 2 / ε := by
  rw [velocity, norm_div, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) hε (clampIm_norm hε _)

lemma norm_velocity_sub_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) (z w : ℂ) :
    ‖velocity ε u z - velocity ε u w‖ ≤ (4 / ε^2) * ‖z-w‖ := by
  let a := clampIm ε (z - (u : ℂ))
  let b := clampIm ε (w - (u : ℂ))
  have ha : a ≠ 0 := clampIm_ne_zero hε _
  have hb : b ≠ 0 := clampIm_ne_zero hε _
  have hna := clampIm_norm hε (z - (u : ℂ))
  have hnb := clampIm_norm hε (w - (u : ℂ))
  have hd : ε^2 ≤ ‖a*b‖ := by
    rw [norm_mul, pow_two]
    exact mul_le_mul hna hnb hε.le (norm_nonneg _)
  have he : velocity ε u z - velocity ε u w = 2 * (b-a) / (a*b) := by
    dsimp [velocity, a, b]
    field_simp [clampIm_ne_zero hε]
  rw [he, norm_div, norm_mul, Complex.norm_ofNat]
  have hn : ‖b-a‖ ≤ 2 * ‖z-w‖ := by
    simpa only [a, b, norm_sub_rev, sub_sub_sub_cancel_right] using
      clampIm_norm_sub ε (z-(u:ℂ)) (w-(u:ℂ))
  calc
    2 * ‖b-a‖ / ‖a*b‖ ≤ (2 * (2 * ‖z-w‖)) / ε^2 :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hn (by norm_num))
        (sq_pos_of_pos hε) hd
    _ = (4 / ε^2) * ‖z-w‖ := by ring

lemma velocity_lipschitz {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    LipschitzWith ⟨4 / ε^2, by positivity⟩ (velocity ε u) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm]
  exact norm_velocity_sub_le hε u z w

lemma continuous_velocity {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun p : ℝ × ℂ => velocity ε p.1 p.2) := by
  unfold velocity clampIm
  refine continuous_const.div ?_ (fun p => clampIm_ne_zero hε _)
  change Continuous (fun p : ℝ × ℂ => Complex.equivRealProdCLM.symm
    ((p.2 - (p.1 : ℂ)).re, max (p.2 - (p.1 : ℂ)).im ε))
  apply Complex.equivRealProdCLM.symm.continuous.comp
  apply Continuous.prodMk <;> fun_prop

lemma exists_solution {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : ℝ → ℝ) (hU : ContinuousOn U (Icc 0 T)) (z : ℂ) :
    ∃ H : ℝ → ℂ, H 0 = z ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t := by
  let L : ℝ≥0 := ⟨2 / ε, by positivity⟩
  let K : ℝ≥0 := ⟨4 / ε^2, by positivity⟩
  let a : ℝ≥0 := ⟨(2 / ε) * T, mul_nonneg (by positivity) hT⟩
  have hp : IsPicardLindelof (fun t => velocity ε (U t))
      ⟨0, ⟨le_rfl, hT⟩⟩ z a 0 L K := by
    constructor
    · exact fun t _ => (velocity_lipschitz hε (U t)).lipschitzOnWith
    · intro w _
      have hc : ContinuousOn (fun t : ℝ => (U t, w)) (Icc 0 T) :=
        hU.prodMk continuousOn_const
      simpa only [Function.comp_def] using
        (continuous_velocity hε).comp_continuousOn hc
    · exact fun t _ w _ => norm_velocity_le hε (U t) w
    · dsimp [L, a]
      simp only [sub_zero, sub_self, max_eq_left hT]
      rfl
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

lemma norm_velocity_driver_sub_le {ε : ℝ} (hε : 0 < ε) (u v : ℝ) (z : ℂ) :
    ‖velocity ε u z - velocity ε v z‖ ≤ (4 / ε^2) * |u-v| := by
  have he (a : ℝ) : velocity ε 0 (z - (a : ℂ)) = velocity ε a z := by
    simp [velocity]
  have hh := norm_velocity_sub_le hε 0 (z-(u:ℂ)) (z-(v:ℂ))
  rw [he, he] at hh
  convert hh using 1
  rw [sub_sub_sub_cancel_left, ← Complex.ofReal_sub, Complex.norm_real, abs_sub_comm]
  simp [Real.norm_eq_abs]

lemma derivWithin_right {ε T : ℝ} {U : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt H (velocity ε (U t) (H t)) (Ici t) t :=
  (hH t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

lemma derivWithin_left {ε T : ℝ} {U : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    HasDerivWithinAt H (velocity ε (U t) (H t)) (Iic t) t :=
  (hH t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht)

lemma solution_eq {ε T : ℝ} (hε : 0 < ε) {U : ℝ → ℝ} {H G : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (velocity ε (U t) (G t)) (Icc 0 T) t)
    (h0 : H 0 = G 0) : EqOn H G (Icc 0 T) := by
  apply ODE_solution_unique_of_mem_Icc_right
    (s := fun _ => univ) (fun t _ => (velocity_lipschitz hε (U t)).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hH) (fun _ ht => derivWithin_right hH ht)
    (fun _ _ => mem_univ _) (HasDerivWithinAt.continuousOn hG)
    (fun _ ht => derivWithin_right hG ht) (fun _ _ => mem_univ _) h0

lemma solution_dist_le {ε T D : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    {U V : ℝ → ℝ} {H G : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (velocity ε (V t) (G t)) (Icc 0 T) t)
    (h0 : H 0 = G 0) (hUV : ∀ t ∈ Icc 0 T, |U t-V t| ≤ D)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (H t) (G t) ≤ D * Real.exp ((4 / ε^2) * T) := by
  let K : ℝ≥0 := ⟨4 / ε^2, by positivity⟩
  have hK : (0 : ℝ) < K := by change 0 < 4 / ε^2; positivity
  have hb (s : ℝ) (hs : s ∈ Ico 0 T) :
      dist (velocity ε (V s) (G s)) (velocity ε (U s) (G s)) ≤ (K : ℝ) * D := by
    rw [dist_eq_norm]
    calc
      _ ≤ (4 / ε^2) * |V s-U s| := norm_velocity_driver_sub_le hε _ _ _
      _ ≤ (K : ℝ) * D := by
        rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (hUV s ⟨hs.1, hs.2.le⟩) hK.le
  have hh := dist_le_of_approx_trajectories_ODE
    (fun t => velocity_lipschitz hε (U t))
    (HasDerivWithinAt.continuousOn hH) (fun _ hs => derivWithin_right hH hs)
    (fun t _ => le_of_eq (dist_self (velocity ε (U t) (H t))))
    (HasDerivWithinAt.continuousOn hG) (fun _ hs => derivWithin_right hG hs)
    hb (le_of_eq (dist_eq_zero.2 h0)) t ht
  have he : gronwallBound 0 K (0 + (K : ℝ)*D) (t-0) =
      D * (Real.exp ((K : ℝ)*t)-1) := by
    simp only [gronwallBound, zero_add, sub_zero, ite_eq_right (ne_of_gt hK)]
    field_simp
    ring
  rw [he] at hh
  have hexp : Real.exp ((K : ℝ)*t) ≤ Real.exp ((K : ℝ)*T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK.le)
  apply hh.trans
  change D * (Real.exp ((4 / ε^2)*t)-1) ≤ D * Real.exp ((4 / ε^2)*T)
  change Real.exp ((4 / ε^2)*t) ≤ Real.exp ((4 / ε^2)*T) at hexp
  exact mul_le_mul_of_nonneg_left (by linarith) hD

end SLEExactGauge.LoewnerCutoff

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.LoewnerCutoff
open scoped unitInterval

def extendDriver (T : ℝ) (U : C(I, ℝ)) (t : ℝ) : ℝ :=
  U (projIcc 0 1 zero_le_one (t / T))

lemma continuous_extendDriver (T : ℝ) (U : C(I, ℝ)) : Continuous (extendDriver T U) :=
  U.continuous.comp (continuous_projIcc.comp (continuous_id.div_const T))

def solution {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) : ℝ → ℂ :=
  (exists_solution hε hT (extendDriver T U) (continuous_extendDriver T U).continuousOn z).choose

lemma solution_initial {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) :
    solution hε hT U z 0 = z :=
  (exists_solution hε hT (extendDriver T U)
    (continuous_extendDriver T U).continuousOn z).choose_spec.1

lemma solution_deriv {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (solution hε hT U z)
      (velocity ε (extendDriver T U t) (solution hε hT U z t)) (Icc 0 T) t :=
  (exists_solution hε hT (extendDriver T U)
    (continuous_extendDriver T U).continuousOn z).choose_spec.2

def solutionPath {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) :
    C(Icc 0 T, ℂ) :=
  ⟨fun t => solution hε hT U z t,
    continuousOn_iff_continuous_domRestrict.1 (HasDerivWithinAt.continuousOn (solution_deriv hε hT U z))⟩

lemma solutionPath_lipschitz {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (z : ℂ) :
    LipschitzWith ⟨Real.exp ((4 / ε^2) * T), (Real.exp_pos _).le⟩
      (fun U : C(I, ℝ) => solutionPath hε hT U z) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  apply (ContinuousMap.dist_le (mul_nonneg (Real.exp_pos _).le dist_nonneg)).2
  intro t
  have hUV (s : ℝ) (_hs : s ∈ Icc 0 T) :
      |extendDriver T U s-extendDriver T V s| ≤ dist U V := by
    exact (ContinuousMap.dist_apply_le_dist (f := U) (g := V)
      (projIcc 0 1 zero_le_one (s/T)))
  have hh := solution_dist_le hε dist_nonneg (solution_deriv hε hT U z)
    (solution_deriv hε hT V z)
    ((solution_initial hε hT U z).trans (solution_initial hε hT V z).symm)
    hUV t.property
  change dist (solution hε hT U z t) (solution hε hT V z t) ≤
    Real.exp ((4 / ε^2)*T) * dist U V
  simpa only [mul_comm] using hh

end SLEExactGauge.LoewnerCutoff

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.ContinuousDriver
section Limit
variable {Ω Y : Type*} [MeasurableSpace Ω] [MetricSpace Y] [CompleteSpace Y]

def selectedLimit (y₀ : Y) (a : ℕ → Y) : Y := by
  classical
  exact if h : CauchySeq a then (cauchySeq_tendsto_of_complete h).choose else y₀

lemma tendsto_selectedLimit (y₀ : Y) {a : ℕ → Y} (h : CauchySeq a) :
    Tendsto a atTop (𝓝 (selectedLimit y₀ a)) := by
  rw [selectedLimit, dite_eq_left h]
  exact (cauchySeq_tendsto_of_complete h).choose_spec

lemma selectedLimit_eq (y₀ : Y) {a : ℕ → Y} {y : Y} (h : Tendsto a atTop (𝓝 y)) :
    selectedLimit y₀ a = y :=
  tendsto_nhds_unique (tendsto_selectedLimit y₀ h.cauchySeq) h

end Limit

end SLEExactGauge.ContinuousDriver

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.ContinuousDriver
section Limit
variable {Ω Y : Type*} [MeasurableSpace Ω] [MetricSpace Y] [completeY : CompleteSpace Y]
variable [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

omit completeY in
lemma measurableSet_cauchy [CompleteSpace Y] (a : ℕ → Ω → Y) (ha : ∀ n, Measurable (a n)) :
    MeasurableSet {ω | CauchySeq (fun n => a n ω)} := by
  simp only [Metric.uniformity_basis_dist_inv_nat_succ.cauchySeq_iff, forall_const,
    mem_ofPred_eq, ofPred_forall, ofPred_exists]
  exact MeasurableSet.iInter fun (k : ℕ) => MeasurableSet.iUnion fun (N : ℕ) =>
    MeasurableSet.iInter fun (m : ℕ) => MeasurableSet.iInter fun (_ : N ≤ m) =>
      MeasurableSet.iInter fun (n : ℕ) => MeasurableSet.iInter fun (_ : N ≤ n) =>
        measurableSet_lt ((ha m).dist (ha n)) measurable_const

lemma measurable_selectedLimit (y₀ : Y) (a : ℕ → Ω → Y) (ha : ∀ n, Measurable (a n)) :
    Measurable (fun ω => selectedLimit y₀ (fun n => a n ω)) := by
  classical
  have hc := measurableSet_cauchy a ha
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => if CauchySeq (fun m => a m ω) then a n ω else y₀)
    (fun n => (ha n).ite hc measurable_const)
  apply tendsto_pi_nhds.2
  intro ω
  by_cases hω : CauchySeq (fun n => a n ω)
  · simpa only [ite_eq_left hω] using tendsto_selectedLimit y₀ hω
  · simp only [ite_eq_right hω, selectedLimit, dite_eq_right hω]
    exact tendsto_const_nhds

end Limit

end SLEExactGauge.ContinuousDriver

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.ContinuousDriver

def rawApprox (x : I → ℝ) (n : ℕ) : C(I, ℝ) :=
  ∑ k : Fin (n+1), (x (bernstein.z k)) • bernstein n k

lemma rawApprox_eq (f : C(I, ℝ)) (n : ℕ) : rawApprox f n = bernsteinApproximation n f := by
  apply ContinuousMap.ext
  intro t
  simp [rawApprox, bernsteinApproximation, smul_eq_mul, mul_comm]

lemma measurable_rawApprox {Ω : Type*} [MeasurableSpace Ω]
    (x : Ω → I → ℝ) (hx : ∀ t, Measurable (fun ω => x ω t)) (n : ℕ) :
    @Measurable Ω C(I, ℝ) _ (borel C(I, ℝ)) (fun ω => rawApprox (x ω) n) := by
  let : MeasurableSpace C(I, ℝ) := borel C(I, ℝ)
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  apply Finset.measurable_sum
  intro k _
  exact (hx (bernstein.z k)).smul measurable_const

def path (x : I → ℝ) : C(I, ℝ) := selectedLimit 0 (rawApprox x)

lemma path_eq (f : C(I, ℝ)) : path f = f := by
  apply selectedLimit_eq
  have he : rawApprox f = fun n => bernsteinApproximation n f :=
    funext (rawApprox_eq f)
  rw [he]
  exact bernsteinApproximation_uniform f

lemma path_eval_of_continuous {x : I → ℝ} (hx : Continuous x) (t : I) : path x t = x t := by
  have hh := path_eq (⟨x, hx⟩ : C(I, ℝ))
  exact congrArg (fun f : C(I, ℝ) => f t) hh

lemma measurable_path {Ω : Type*} [MeasurableSpace Ω]
    (x : Ω → I → ℝ) (hx : ∀ t, Measurable (fun ω => x ω t)) :
    @Measurable Ω C(I, ℝ) _ (borel C(I, ℝ)) (fun ω => path (x ω)) := by
  let : MeasurableSpace C(I, ℝ) := borel C(I, ℝ)
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  exact measurable_selectedLimit 0 _ (measurable_rawApprox x hx)

end SLEExactGauge.ContinuousDriver

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.LoewnerCutoff
open scoped unitInterval

def position {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℂ :=
  solutionPath hε hT U z (projIcc 0 T hT t)

lemma position_eq {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    position hε hT U z t = solution hε hT U z t := by
  simp only [position, solutionPath, projIcc, max_eq_right ht.1,
    min_eq_right ht.2]
  rfl

lemma continuous_position {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (z : ℂ) :
    Continuous (fun p : C(I, ℝ) × ℝ => position hε hT p.1 z p.2) := by
  exact continuous_eval.comp (((solutionPath_lipschitz hε hT z).continuous.comp continuous_fst).prodMk
    ((continuous_projIcc (h := hT)).comp continuous_snd))

lemma continuous_joint_extendDriver (T : ℝ) :
    Continuous (fun p : C(I, ℝ) × ℝ => extendDriver T p.1 p.2) := by
  exact continuous_eval.comp (continuous_fst.prodMk
    ((continuous_projIcc (h := zero_le_one)).comp (continuous_snd.div_const T)))

def variation {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℝ :=
  (-2 / (clampIm ε (position hε hT U z t - (extendDriver T U t : ℂ)))^2).re

lemma continuous_clampIm (ε : ℝ) : Continuous (clampIm ε) := by
  change Continuous (fun w : ℂ => Complex.equivRealProdCLM.symm (w.re,max w.im ε))
  apply Complex.equivRealProdCLM.symm.continuous.comp
  apply Continuous.prodMk <;> fun_prop

lemma continuous_variation {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (z : ℂ) :
    Continuous (fun p : C(I, ℝ) × ℝ => variation hε hT p.1 z p.2) := by
  have hw := (continuous_position hε hT z).sub
    (Complex.continuous_ofReal.comp (continuous_joint_extendDriver T))
  exact Complex.continuous_re.comp (continuous_const.div
    (((continuous_clampIm ε).comp hw).pow 2)
    (fun p => pow_ne_zero 2 (clampIm_ne_zero hε _)))

def logDerivative {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..(projIcc 0 T hT t : ℝ), variation hε hT U z s

lemma continuous_logDerivative {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (z : ℂ) :
    Continuous (fun p : C(I, ℝ) × ℝ => logDerivative hε hT p.1 z p.2) := by
  have hc := intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := volume) (a₀ := 0) (f := fun U t => variation hε hT U z t)
    (continuous_variation hε hT z)
  exact hc.comp (continuous_fst.prodMk
    (continuous_subtype_val.comp ((continuous_projIcc (h := hT)).comp continuous_snd)))

lemma abs_variation_le {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) (t : ℝ) :
    |variation hε hT U z t| ≤ 2/ε^2 := by
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_div, norm_neg, Complex.norm_ofNat, norm_pow]
  apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hε)
  exact pow_le_pow_left₀ hε.le (clampIm_norm hε _) 2

lemma logDerivative_initial {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) : logDerivative hε hT U z 0 = 0 := by
  simp only [logDerivative, projIcc_of_mem hT (left_mem_Icc.mpr hT), intervalIntegral.integral_same]

lemma abs_logDerivative_le {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) (t : ℝ) :
    |logDerivative hε hT U z t| ≤ (2/ε^2)*T := by
  have hb := (projIcc 0 T hT t).property
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := (projIcc 0 T hT t : ℝ))
    (fun s (_hs : s ∈ uIoc 0 (projIcc 0 T hT t : ℝ)) =>
      show ‖variation hε hT U z s‖ ≤ 2/ε^2 from abs_variation_le hε hT U z s)
  change |logDerivative hε hT U z t| ≤ _
  apply hi.trans
  rw [sub_zero, abs_of_nonneg hb.1]
  exact mul_le_mul_of_nonneg_left hb.2 (by positivity)

lemma position_initial {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) : position hε hT U z 0 = z := by
  rw [position_eq hε hT U z ⟨le_rfl,hT⟩, solution_initial]

lemma position_derivWithin {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (position hε hT U z)
      (velocity ε (extendDriver T U t) (position hε hT U z t)) (Icc 0 T) t := by
  rw [position_eq hε hT U z ht]
  exact (solution_deriv hε hT U z t ht).congr
    (fun s hs => position_eq hε hT U z hs) (position_eq hε hT U z ht)

lemma position_deriv {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (position hε hT U z)
      (velocity ε (extendDriver T U t) (position hε hT U z t)) t :=
  (position_derivWithin hε hT U z ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

lemma logDerivative_eq_integral {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    logDerivative hε hT U z t = ∫ s in (0:ℝ)..t, variation hε hT U z s := by
  simp only [logDerivative, projIcc_of_mem hT ht]

lemma hasDerivAt_logDerivative {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (logDerivative hε hT U z) (variation hε hT U z t) t := by
  have hp : Continuous (fun t : ℝ => (U,t)) := continuous_const.prodMk continuous_id
  have hc := (continuous_variation hε hT z).comp hp
  dsimp only [Function.comp_def] at hc
  have hd : HasDerivAt (fun v : ℝ => ∫ s in (0:ℝ)..v, variation hε hT U z s)
      (variation hε hT U z t) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  exact logDerivative_eq_integral hε hT U z hs

lemma position_prefix_eq {ε T₁ T₂ S : ℝ} (hε : 0 < ε)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) (_hS : 0 ≤ S) (hS₁ : S ≤ T₁) (hS₂ : S ≤ T₂)
    (U V : C(I, ℝ)) (z : ℂ)
    (hUV : EqOn (extendDriver T₁ U) (extendDriver T₂ V) (Icc 0 S)) :
    EqOn (position hε hT₁ U z) (position hε hT₂ V z) (Icc 0 S) := by
  apply solution_eq hε (U := extendDriver T₁ U) ?_ ?_ ((position_initial hε hT₁ U z).trans (position_initial hε hT₂ V z).symm)
  · intro t ht
    exact (position_derivWithin hε hT₁ U z ⟨ht.1,ht.2.trans hS₁⟩).mono
      (Icc_subset_Icc le_rfl hS₁)
  · intro t ht
    rw [hUV ht]
    exact (position_derivWithin hε hT₂ V z ⟨ht.1,ht.2.trans hS₂⟩).mono
      (Icc_subset_Icc le_rfl hS₂)

lemma logDerivative_prefix_eq {ε T₁ T₂ S : ℝ} (hε : 0 < ε)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) (hS : 0 ≤ S) (hS₁ : S ≤ T₁) (hS₂ : S ≤ T₂)
    (U V : C(I, ℝ)) (z : ℂ)
    (hUV : EqOn (extendDriver T₁ U) (extendDriver T₂ V) (Icc 0 S)) :
    EqOn (logDerivative hε hT₁ U z) (logDerivative hε hT₂ V z) (Icc 0 S) := by
  have hH := position_prefix_eq hε hT₁ hT₂ hS hS₁ hS₂ U V z hUV
  intro t ht
  rw [logDerivative_eq_integral hε hT₁ U z ⟨ht.1,ht.2.trans hS₁⟩,
    logDerivative_eq_integral hε hT₂ V z ⟨ht.1,ht.2.trans hS₂⟩]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  have hsS : s ∈ Icc 0 S := ⟨hs.1,hs.2.trans ht.2⟩
  simp only [variation, hH hsS, hUV hsS]

end SLEExactGauge.LoewnerCutoff

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SLEExactGauge.GreenPhysical

def green (p a x y l : ℝ) : ℝ :=
  Real.exp (p*l - p*Real.log 2 + (a-p)*Real.log y - a/2*Real.log (x^2+y^2))

lemma q_pos (x : ℝ) {y : ℝ} (hy : 0 < y) : 0 < x^2+y^2 := by positivity

lemma green_eq_source (p a x y l : ℝ) (hy : 0 < y) :
    green p a x y l = (2*y / Real.exp l)^(-p) * (y / Real.sqrt (x^2+y^2))^a := by
  have hQ := q_pos x hy
  have hR : 0 < 2*y / Real.exp l := div_pos (by positivity) (Real.exp_pos _)
  have hS : 0 < y / Real.sqrt (x^2+y^2) := div_pos hy (Real.sqrt_pos.2 hQ)
  rw [Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hS, ← Real.exp_add]
  dsimp [green]
  congr 1
  rw [Real.log_div (by positivity : 2*y ≠ 0) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hy.ne', Real.log_exp,
    Real.log_div hy.ne' (by positivity : Real.sqrt (x^2+y^2) ≠ 0),
    Real.log_sqrt hQ.le]
  ring

lemma green_pos (p a x y l : ℝ) : 0 < green p a x y l := Real.exp_pos _

lemma hasDerivAt_green_path (p a : ℝ) {X Y L : ℝ → ℝ} {t X' Y' L' : ℝ}
    (hX : HasDerivAt X X' t) (hY : HasDerivAt Y Y' t) (hL : HasDerivAt L L' t)
    (hy : 0 < Y t) :
    HasDerivAt (fun u => green p a (X u) (Y u) (L u))
      (green p a (X t) (Y t) (L t) *
        (p*L' + (a-p)*Y'/Y t - a*(X t*X' + Y t*Y')/(X t^2+Y t^2))) t := by
  have hlogY := hY.log hy.ne'
  have hlogQ := ((hX.pow 2).add (hY.pow 2)).log (q_pos (X t) hy).ne'
  have hd := ((((hL.const_mul p).sub_const (p*Real.log 2)).add
    (hlogY.const_mul (a-p))).sub (hlogQ.const_mul (a/2))).exp
  apply hd.congr_deriv
  dsimp [green]
  ring

lemma hasDerivAt_green_x (p a x y l : ℝ) (hy : 0 < y) :
    HasDerivAt (fun u => green p a u y l) (green p a x y l * (-a*x/(x^2+y^2))) x := by
  convert hasDerivAt_green_path p a (hasDerivAt_id x) (hasDerivAt_const x y)
    (hasDerivAt_const x l) hy using 1 <;> dsimp only [id_eq]; ring

lemma deriv_green_x (p a x y l : ℝ) (hy : 0 < y) :
    deriv (fun u => green p a u y l) x = green p a x y l * (-a*x/(x^2+y^2)) :=
  (hasDerivAt_green_x p a x y l hy).deriv

lemma hasDerivAt_neg_ax_div_q (a x y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun u => -a*u/(u^2+y^2))
      (a*(x^2-y^2)/(x^2+y^2)^2) x := by
  have hd := ((hasDerivAt_id x).const_mul (-a)).div
    (((hasDerivAt_id x).pow 2).add_const (y^2)) (q_pos x hy).ne'
  apply hd.congr_deriv
  simp only [id_eq, Pi.pow_apply]
  norm_num
  ring

lemma deriv_deriv_green_x (p a x y l : ℝ) (hy : 0 < y) :
    deriv (deriv (fun u => green p a u y l)) x =
      green p a x y l * (a*(a+1)*x^2-a*y^2)/(x^2+y^2)^2 := by
  have heq : deriv (fun u => green p a u y l) =
      (fun u => green p a u y l * (-a*u/(u^2+y^2))) :=
    funext (fun u => deriv_green_x p a u y l hy)
  rw [heq]
  have hd := (hasDerivAt_green_x p a x y l hy).mul (hasDerivAt_neg_ax_div_q a x y hy)
  calc
    _ = _ := hd.deriv
    _ = _ := by
      field_simp
      ring

lemma green_drift_cancellation (κ x y M : ℝ) (hκ : κ ≠ 0) (hy : 0 < y) :
    let p := 1-κ/8
    let a := 8/κ-1
    M * (p * (-2*(x^2-y^2)/(x^2+y^2)^2) +
      (a-p) * (-2*y/(x^2+y^2))/y -
      a * (x*(2*x/(x^2+y^2)) + y*(-2*y/(x^2+y^2)))/(x^2+y^2)) +
    κ/2 * (M*(a*(a+1)*x^2-a*y^2)/(x^2+y^2)^2) = 0 := by
  dsimp only
  field_simp
  ring

lemma loewner_green_drift {κ t : ℝ} (hκ : 0 < κ) {X Y L : ℝ → ℝ}
    (hy : 0 < Y t)
    (hX : HasDerivAt X (2*X t/(X t^2+Y t^2)) t)
    (hY : HasDerivAt Y (-2*Y t/(X t^2+Y t^2)) t)
    (hL : HasDerivAt L (-2*(X t^2-Y t^2)/(X t^2+Y t^2)^2) t) :
    HasDerivAt (fun u => green (1-κ/8) (8/κ-1) (X u) (Y u) (L u))
      (-(κ/2) * deriv (deriv (fun x => green (1-κ/8) (8/κ-1) x (Y t) (L t))) (X t)) t := by
  have hd := hasDerivAt_green_path (1-κ/8) (8/κ-1) hX hY hL hy
  apply hd.congr_deriv
  rw [deriv_deriv_green_x _ _ _ _ _ hy]
  have hc := green_drift_cancellation κ (X t) (Y t)
    (green (1-κ/8) (8/κ-1) (X t) (Y t) (L t)) hκ.ne' hy
  dsimp only at hc
  linarith

lemma hasDerivAt_green_driver (p a c y l sdev b : ℝ) (hy : 0 < y) :
    HasDerivAt (fun v => green p a (c-sdev*v) y l)
      (sdev*a*(c-sdev*b)/((c-sdev*b)^2+y^2) * green p a (c-sdev*b) y l) b := by
  have hd := (hasDerivAt_green_x p a (c-sdev*b) y l hy).comp b
    (((hasDerivAt_id b).const_mul sdev).const_sub c)
  apply hd.congr_deriv
  ring

lemma deriv_green_driver (p a c y l sdev b : ℝ) (hy : 0 < y) :
    deriv (fun v => green p a (c-sdev*v) y l) b =
      sdev*a*(c-sdev*b)/((c-sdev*b)^2+y^2) * green p a (c-sdev*b) y l :=
  (hasDerivAt_green_driver p a c y l sdev b hy).deriv

lemma hasDerivAt_deriv_green_x (p a x y l : ℝ) (hy : 0 < y) :
    HasDerivAt (deriv (fun u => green p a u y l))
      (green p a x y l * (a*(a+1)*x^2-a*y^2)/(x^2+y^2)^2) x := by
  have heq : deriv (fun u => green p a u y l) =
      (fun u => green p a u y l * (-a*u/(u^2+y^2))) :=
    funext (fun u => deriv_green_x p a u y l hy)
  rw [heq]
  apply ((hasDerivAt_green_x p a x y l hy).mul (hasDerivAt_neg_ax_div_q a x y hy)).congr_deriv
  field_simp
  ring

lemma deriv_deriv_green_driver (p a c y l sdev b : ℝ) (hy : 0 < y) :
    deriv (deriv (fun v => green p a (c-sdev*v) y l)) b =
      sdev^2 * (green p a (c-sdev*b) y l *
        (a*(a+1)*(c-sdev*b)^2-a*y^2)/((c-sdev*b)^2+y^2)^2) := by
  have heq : deriv (fun v => green p a (c-sdev*v) y l) =
      fun v => (-sdev) * deriv (fun u => green p a u y l) (c-sdev*v) := by
    ext v
    rw [deriv_green_driver _ _ _ _ _ _ _ hy, deriv_green_x _ _ _ _ _ hy]
    ring
  rw [heq]
  have hd := ((hasDerivAt_deriv_green_x p a (c-sdev*b) y l hy).comp b
    (((hasDerivAt_id b).const_mul sdev).const_sub c)).const_mul (-sdev)
  calc
    _ = _ := hd.deriv
    _ = _ := by ring

lemma green_le_radius (p a x y l : ℝ) (hy : 0 < y) (ha : 0 ≤ a) :
    green p a x y l ≤ (2*y/Real.exp l)^(-p) := by
  rw [green_eq_source _ _ _ _ _ hy]
  have hQ := q_pos x hy
  have hyS : y ≤ Real.sqrt (x^2+y^2) := by
    rw [Real.le_sqrt hy.le (by positivity)]
    nlinarith [sq_nonneg x]
  have hr : 0 ≤ (2*y/Real.exp l)^(-p) := Real.rpow_nonneg (by positivity) _
  have hs : (y/Real.sqrt (x^2+y^2))^a ≤ 1 :=
    Real.rpow_le_one (by positivity) ((div_le_one (Real.sqrt_pos.2 hQ)).2 hyS) ha
  simpa using mul_le_mul_of_nonneg_left hs hr

lemma green_le_fixed_radius (p a x y l ρ : ℝ) (hy : 0 < y) (ha : 0 ≤ a)
    (hp : 0 ≤ p) (hρ : 0 < ρ) (hR : ρ ≤ 2*y/Real.exp l) :
    green p a x y l ≤ ρ^(-p) := by
  exact (green_le_radius p a x y l hy ha).trans
    (Real.rpow_le_rpow_of_nonpos hρ hR (neg_nonpos.2 hp))

lemma contDiff_green_x (p a y l : ℝ) (hy : 0 < y) {n : ℕ∞ω} :
    ContDiff ℝ n (fun x => green p a x y l) := by
  unfold green
  apply ContDiff.exp
  apply ContDiff.sub contDiff_const
  exact contDiff_const.mul (((contDiff_id.pow 2).add contDiff_const).log
    (fun x => (q_pos x hy).ne'))

lemma contDiff_green_driver (p a c y l sdev : ℝ) (hy : 0 < y) {n : ℕ∞ω} :
    ContDiff ℝ n (fun b => green p a (c-sdev*b) y l) :=
  (contDiff_green_x p a y l hy).comp (contDiff_const.sub (contDiff_const.mul contDiff_id))

lemma hasDerivAt_second_green_x (p a x y l : ℝ) (hy : 0 < y) :
    HasDerivAt (deriv (deriv (fun v => green p a v y l)))
      (green p a x y l * (a*(a+2)*x*(3*y^2-(a+1)*x^2))/(x^2+y^2)^3) x := by
  have he : deriv (deriv (fun v => green p a v y l)) =
      fun v => green p a v y l * (a*(a+1)*v^2-a*y^2)/(v^2+y^2)^2 :=
    funext (fun v => deriv_deriv_green_x p a v y l hy)
  rw [he]
  have hn := (hasDerivAt_green_x p a x y l hy).mul
    ((((hasDerivAt_id x).pow 2).const_mul (a*(a+1))).sub_const (a*y^2))
  have hq := (((hasDerivAt_id x).pow 2).add_const (y^2)).pow 2
  apply (hn.div hq (pow_ne_zero 2 (q_pos x hy).ne')).congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.mul_apply]
  field_simp
  ring

lemma third_green_x (p a x y l : ℝ) (hy : 0 < y) :
    iteratedDeriv 3 (fun v => green p a v y l) x =
      green p a x y l * (a*(a+2)*x*(3*y^2-(a+1)*x^2))/(x^2+y^2)^3 := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    (hasDerivAt_second_green_x p a x y l hy).deriv

lemma iteratedDeriv_green_driver (p a c y l sdev : ℝ) (hy : 0 < y) (k : ℕ) (b : ℝ) :
    iteratedDeriv k (fun v => green p a (c-sdev*v) y l) b =
      (-sdev)^k * iteratedDeriv k (fun x => green p a x y l) (c-sdev*b) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    have he : iteratedDeriv k (fun v => green p a (c-sdev*v) y l) =
        fun v => (-sdev)^k * iteratedDeriv k (fun x => green p a x y l) (c-sdev*v) := funext ih
    rw [iteratedDeriv_succ, he]
    have hd : Differentiable ℝ (iteratedDeriv k (fun x => green p a x y l)) :=
      ContDiff.differentiable_iteratedDeriv k (contDiff_green_x p a y l hy (n := ⊤)) (by simp)
    have hh := ((hd (c-sdev*b)).hasDerivAt.comp b
      (((hasDerivAt_id b).const_mul sdev).const_sub c)).const_mul ((-sdev)^k)
    dsimp only [Function.comp_def, id_eq] at hh
    rw [hh.deriv]
    simp only [iteratedDeriv_succ, pow_succ, mul_one]
    ring

lemma abs_x_div_q_le {ε y : ℝ} (hε : 0 < ε) (hy : ε ≤ y) (x : ℝ) :
    |x| / (x^2+y^2) ≤ 1/ε := by
  have hq := q_pos x (hε.trans_le hy)
  apply (div_le_div_iff₀ hq hε).2
  have hεy : ε^2 ≤ y^2 := pow_le_pow_left₀ hε.le hy 2
  nlinarith [sq_nonneg (|x|-ε), sq_abs x, sq_nonneg x]

lemma inv_q_le {ε y : ℝ} (hε : 0 < ε) (hy : ε ≤ y) (x : ℝ) :
    1/(x^2+y^2) ≤ 1/ε^2 := by
  apply div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hε)
  exact (pow_le_pow_left₀ hε.le hy 2).trans (le_add_of_nonneg_left (sq_nonneg x))

lemma third_green_bound {p a x y l ε M : ℝ} (hε : 0 < ε) (hy : ε ≤ y)
    (ha : 0 ≤ a) (hM : green p a x y l ≤ M) :
    |iteratedDeriv 3 (fun v => green p a v y l) x| ≤
      M * (a*(a+2)*(a+4)) / ε^3 := by
  have hypos := hε.trans_le hy
  have hq := q_pos x hypos
  have hMp : 0 ≤ M := (green_pos p a x y l).le.trans hM
  have hP : |3*y^2-(a+1)*x^2| ≤ (a+4)*(x^2+y^2) := by
    calc
      _ ≤ |3*y^2| + |(a+1)*x^2| := abs_sub _ _
      _ = 3*y^2+(a+1)*x^2 := by rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ _ := by nlinarith [mul_nonneg ha (sq_nonneg y), sq_nonneg x]
  rw [third_green_x _ _ _ _ _ hypos]
  simp only [abs_div, abs_mul, abs_pow, abs_of_pos hq, abs_of_pos (green_pos p a x y l),
    abs_of_nonneg ha, abs_of_nonneg (show 0 ≤ a+2 by linarith)]
  calc
    _ ≤ M * (a*(a+2)* |x| *((a+4)*(x^2+y^2))) / (x^2+y^2)^3 := by
      gcongr
    _ = M*(a*(a+2)*(a+4)) * (|x|/(x^2+y^2)) * (1/(x^2+y^2)) := by
      field_simp
    _ ≤ M*(a*(a+2)*(a+4)) * (1/ε) * (1/ε^2) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (abs_x_div_q_le hε hy x) (by positivity))
        (inv_q_le hε hy x) (by positivity) (by positivity)
    _ = _ := by ring

lemma continuous_green_comp {X : Type*} [TopologicalSpace X]
    (p a : ℝ) {x y l : X → ℝ} (hx : Continuous x) (hy : Continuous y)
    (hl : Continuous l) (hyp : ∀ t, 0 < y t) :
    Continuous (fun t => green p a (x t) (y t) (l t)) := by
  unfold green
  apply Real.continuous_exp.comp
  exact (((continuous_const.mul hl).sub continuous_const).add
    (continuous_const.mul (hy.log (fun t => (hyp t).ne')))).sub
    (continuous_const.mul (((hx.pow 2).add (hy.pow 2)).log
      (fun t => (q_pos (x t) (hyp t)).ne')))

lemma first_green_bound {p a x y l ε M : ℝ} (hε : 0 < ε) (hy : ε ≤ y)
    (ha : 0 ≤ a) (hM : green p a x y l ≤ M) :
    |deriv (fun v => green p a v y l) x| ≤ M*a/ε := by
  have hp := green_pos p a x y l
  rw [deriv_green_x p a x y l (hε.trans_le hy)]
  simp only [abs_mul, abs_div, abs_neg, abs_of_nonneg ha,
    abs_of_pos (q_pos x (hε.trans_le hy)), abs_of_pos hp]
  calc
    _ = green p a x y l * a * (|x|/(x^2+y^2)) := by ring
    _ ≤ M*a*(1/ε) := mul_le_mul
      (mul_le_mul_of_nonneg_right hM ha) (abs_x_div_q_le hε hy x)
      (by positivity) (mul_nonneg (hp.le.trans hM) ha)
    _ = _ := by ring

lemma second_green_bound {p a x y l ε M : ℝ} (hε : 0 < ε) (hy : ε ≤ y)
    (ha : 0 ≤ a) (hM : green p a x y l ≤ M) :
    |iteratedDeriv 2 (fun v => green p a v y l) x| ≤ M*(a*(a+2))/ε^2 := by
  have hp := green_pos p a x y l
  have hMp : 0 ≤ M := hp.le.trans hM
  have hq := q_pos x (hε.trans_le hy)
  have hP : |a*(a+1)*x^2-a*y^2| ≤ a*(a+2)*(x^2+y^2) := by
    calc
      _ ≤ |a*(a+1)*x^2|+|a*y^2| := abs_sub _ _
      _ = a*(a+1)*x^2+a*y^2 := by rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ _ := by nlinarith [mul_nonneg ha (sq_nonneg x), mul_nonneg (mul_nonneg ha (by positivity : 0 ≤ a+1)) (sq_nonneg y)]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [deriv_deriv_green_x p a x y l (hε.trans_le hy)]
  simp only [abs_div, abs_mul, abs_pow, abs_of_pos hq, abs_of_pos hp]
  calc
    _ ≤ M*(a*(a+2)*(x^2+y^2))/(x^2+y^2)^2 := by gcongr
    _ = M*(a*(a+2))*(1/(x^2+y^2)) := by field_simp
    _ ≤ M*(a*(a+2))*(1/ε^2) := mul_le_mul_of_nonneg_left (inv_q_le hε hy x) (by positivity)
    _ = _ := by ring

end SLEExactGauge.GreenPhysical

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SLEExactGauge.LoewnerField
open LoewnerCutoff GreenPhysical
open scoped unitInterval
variable {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)

def height (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℝ :=
  max ε (position hε hT U z t).im

def field (p a sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) : ℝ :=
  green p a ((position hε hT U z t).re - sdev*b) (height hε hT U z t)
    (logDerivative hε hT U z t)

def drift (p a sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) : ℝ :=
  let x := (position hε hT U z t).re - sdev*b
  let y := height hε hT U z t
  let v := velocity ε (extendDriver T U t) (position hε hT U z t)
  field hε hT p a sdev U z t b *
    (p*variation hε hT U z t + (a-p)*v.im/y - a*(x*v.re+y*v.im)/(x^2+y^2))

end SLEExactGauge.LoewnerField

end

end

end

end

end

end

end

end

end OAI
