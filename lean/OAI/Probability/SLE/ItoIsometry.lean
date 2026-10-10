import Mathlib
import OAI.Probability.SLE.IntegralLimits

namespace OAI

/-! Ito Isometry for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.TimeField
open TaylorMeshes
lemma mesh_family_remainder_tendsto {f : ℕ → ℕ → ℝ → ℝ} {b : ℝ → ℝ}
    (hf : ∀ n i, ContDiff ℝ 3 (f n i))
    {T V K : ℝ} (hT : 0 ≤ T) (hb : ContinuousOn b (Icc 0 T)) (hK : 0 ≤ K)
    (h3 : ∀ n i x, |iteratedDeriv 3 (f n i) x| ≤ K)
    (hQ : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1)) - b (mesh T n i))^2) atTop (𝓝 V)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      remainder₂ (f n i) (b (mesh T n i)) (b (mesh T n (i+1)))) atTop (𝓝 0) := by
  have hV : 0 ≤ V := ge_of_tendsto hQ (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ := ε / ((K+1)*(V+1))
  have hδ : 0 < δ := div_pos hε (mul_pos (by linarith) (by linarith))
  have hs := mesh_increments_small hT hb hδ
  have hq := hQ.eventually (gt_mem_nhds (show V < V+1 by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.and hq)
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨hs, hq⟩
  have hr := sum_family_remainder₂_bound (hf n) (fun i => b (mesh T n i)) (2^n) K δ hK hδ.le
    (fun i _ z _ => h3 n i z) (fun i hi => (hs i hi).le)
  simp only [Real.dist_eq, sub_zero]
  calc
    _ ≤ K * δ / 6 * ∑ i ∈ Finset.range (2^n),
        (b (mesh T n (i+1)) - b (mesh T n i))^2 := hr
    _ ≤ K * δ / 6 * (V+1) := mul_le_mul_of_nonneg_left hq.le (by positivity)
    _ < ε := by
      dsimp [δ]
      have hden : 0 < (K+1)*(V+1) := mul_pos (by linarith) (by linarith)
      have hid : K * (ε / ((K+1)*(V+1))) / 6 * (V+1) = ε * (K / (6*(K+1))) := by
        field_simp
      rw [hid]
      have hk : K / (6*(K+1)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      simpa using mul_lt_mul_of_pos_left hk hε

 

lemma mesh_time_increment_tendsto {F V : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hF : ∀ x, ContinuousOn (fun t => F t x) (Icc 0 T))
    (hD : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun u => F u x) (V t x) t)
    (hV : ContinuousOn (fun p : ℝ × ℝ => V p.1 (b p.2)) ((Icc 0 T) ×ˢ (Icc 0 T))) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (F (mesh T n (i+1)) (b (mesh T n (i+1))) -
        F (mesh T n i) (b (mesh T n (i+1))))) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, V t (b t))) := by
  rcases hT.eq_or_lt with hT | hT
  · subst T
    simp [mesh]
  have hVc : ContinuousOn (fun t => V t (b t)) (Icc 0 T) :=
    hV.comp (continuousOn_id.prodMk continuousOn_id) (fun t ht => ⟨ht, ht⟩)
  have hriem := mesh_riemann_tendsto hT.le hVc
  have herror : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (F (mesh T n (i+1)) (b (mesh T n (i+1))) -
        F (mesh T n i) (b (mesh T n (i+1))) -
          V (mesh T n i) (b (mesh T n i)) * (T / (2 : ℝ)^n))) atTop (𝓝 0) := by
    have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hV
    apply Metric.tendsto_atTop.2
    intro ε hε
    let ζ : ℝ := ε / (T+1)
    have hζ : 0 < ζ := div_pos hε (by linarith)
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 hu ζ hζ
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((mesh_step_tendsto T).eventually (gt_mem_nhds hδ))
    refine ⟨N, fun n hn => ?_⟩
    have hnδ := hN n hn
    have heach (i : ℕ) (hi : i < 2^n) :
        |F (mesh T n (i+1)) (b (mesh T n (i+1))) -
          F (mesh T n i) (b (mesh T n (i+1))) -
            V (mesh T n i) (b (mesh T n i)) * (T / (2 : ℝ)^n)| ≤
        ζ * (T / (2 : ℝ)^n) := by
      have hstep_pos : mesh T n i < mesh T n (i+1) := by
        have : 0 < mesh T n (i+1) - mesh T n i := by rw [mesh_step]; positivity
        linarith
      have hleft := mesh_mem T hT.le n i hi.le
      have hright := mesh_mem T hT.le n (i+1) hi
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
        (fun t => F t (b (mesh T n (i+1)))) (fun t => V t (b (mesh T n (i+1))))
        hstep_pos ((hF _).mono (Icc_subset_Icc hleft.1 hright.2))
        (fun t ht => hD t ⟨hleft.1.trans_lt ht.1, ht.2.trans_le hright.2⟩ _)
      have hcT : c ∈ Icc 0 T := ⟨hleft.1.trans hc.1.le, hc.2.le.trans hright.2⟩
      have hdist : dist (c, mesh T n (i+1)) (mesh T n i, mesh T n i) < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        constructor
        · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hc.1.le)]
          have hcs := hc.2
          have hstep := mesh_step T n i
          linarith
        · rw [Real.dist_eq, mesh_step, abs_of_nonneg (by positivity)]
          exact hnδ
      have hvmod := (hmod (c, mesh T n (i+1)) ⟨hcT, hright⟩
        (mesh T n i, mesh T n i) ⟨hleft, hleft⟩ hdist).le
      simp only [Real.dist_eq] at hvmod
      have hid : F (mesh T n (i+1)) (b (mesh T n (i+1))) -
          F (mesh T n i) (b (mesh T n (i+1))) =
          V c (b (mesh T n (i+1))) * (T / (2 : ℝ)^n) := by
        rw [mesh_step] at heq
        exact (eq_div_iff (ne_of_gt (div_pos hT (by positivity)))).1 heq |>.symm
      rw [hid, ← sub_mul, abs_mul, abs_of_nonneg (show 0 ≤ T / (2 : ℝ)^n by positivity)]
      exact mul_le_mul_of_nonneg_right hvmod (by positivity)
    rw [Real.dist_eq, sub_zero]
    calc
      _ ≤ ∑ i ∈ Finset.range (2^n),
          |F (mesh T n (i+1)) (b (mesh T n (i+1))) -
            F (mesh T n i) (b (mesh T n (i+1))) -
              V (mesh T n i) (b (mesh T n i)) * (T / (2 : ℝ)^n)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (2^n), ζ * (T / (2 : ℝ)^n) :=
        Finset.sum_le_sum (fun i hi => heach i (Finset.mem_range.1 hi))
      _ = ζ * T := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        field_simp
      _ < ε := by
        dsimp [ζ]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < T+1)]
        nlinarith
  have hadd := herror.add hriem
  simp only [Finset.sum_sub_distrib, sub_add_cancel, zero_add] at hadd
  simpa only [Finset.sum_sub_distrib] using hadd

end SLEExactGauge.TimeField

namespace SLEExactGauge.BrownianIto
open BrownianPredictable TaylorMeshes

lemma coe_dyadicTime (T : ℝ≥0) (n i : ℕ) :
    (dyadicTime T n i : ℝ) = mesh T n i := by
  simp only [dyadicTime, mesh]
  push_cast
  rfl

lemma mesh_toNNReal (T : ℝ≥0) (n i : ℕ) :
    (mesh T n i).toNNReal = dyadicTime T n i := by
  rw [← coe_dyadicTime]
  exact Real.toNNReal_coe

 
def derivativeSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (f : ℝ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n), deriv f (B (dyadicTime T n i) ω) *
    (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)

def quadraticSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n),
    (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)^2

lemma error_one_eq {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) :
    dyadicQuadraticError B T (fun _ _ _ => 1) n ω = quadraticSum B T n ω - T := by
  simp only [dyadicQuadraticError, one_mul, Finset.sum_sub_distrib, quadraticSum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  congr 1
  field_simp

lemma quadraticSum_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => quadraticSum B T n ω) atTop (𝓝 (T : ℝ)) := by
  have he := brownian_dyadic_weighted_quadraticError_tendsto hB T (fun _ _ _ => 1)
    (fun _ _ => measurable_const) (fun _ _ => memLp_const _) 1 (by norm_num)
    (fun _ _ => Eventually.of_forall fun _ => by norm_num)
  simp only [error_one_eq] at he
  filter_upwards [he] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add_const (T : ℝ)

end SLEExactGauge.BrownianIto

namespace SLEExactGauge.BrownianField
open BrownianPredictable PredictableLimit TaylorMeshes TimeField BrownianIto

def fieldSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (F : Ω → ℝ → ℝ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n), deriv (F ω (mesh T n i)) (B (dyadicTime T n i) ω) *
    (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)

 

structure FieldRegular (F V : ℝ → ℝ → ℝ) (b : ℝ → ℝ) (T : ℝ) : Prop where
  smooth : ∀ t, ContDiff ℝ 3 (F t)
  third_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t x, |iteratedDeriv 3 (F t) x| ≤ K
  time_cont : ∀ x, ContinuousOn (fun t => F t x) (Icc 0 T)
  time_deriv : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun u => F u x) (V t x) t
  drift_cont : ContinuousOn (fun p : ℝ × ℝ => V p.1 (b p.2)) ((Icc 0 T) ×ˢ (Icc 0 T))
  second_cont : ContinuousOn (fun t => iteratedDeriv 2 (F t) (b t)) (Icc 0 T)

 

theorem fieldSum_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (F V : Ω → ℝ → ℝ → ℝ)
    (hreg : ∀ᵐ ω ∂P, FieldRegular (F ω) (V ω) (fun t => B t.toNNReal ω) T)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)]
      (fun ω => iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)))
    (hC2 : ∀ n i, MemLp
      (fun ω => iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)) 2 P)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hbound : ∀ n i, ∀ᵐ ω ∂P,
      |iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)| ≤ K₂) :
    ∀ᵐ ω ∂P, Tendsto (fun n => fieldSum B T F n ω) atTop
      (𝓝 (F ω T (B T ω) - F ω 0 (B 0 ω) -
        (∫ t in (0 : ℝ)..(T : ℝ), V ω t (B t.toNNReal ω)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(T : ℝ),
          iteratedDeriv 2 (F ω t) (B t.toNNReal ω))) := by
  let C : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)
  have he := brownian_dyadic_weighted_quadraticError_tendsto hB T C hC hC2 K₂ hK₂ hbound
  filter_upwards [hB.cont, quadraticSum_tendsto hB T, he, hreg] with ω hcω hQω heω hrω
  let b : ℝ → ℝ := fun t => B t.toNNReal ω
  have hb : Continuous b := hcω.comp continuous_real_toNNReal
  have hQ : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1))-b (mesh T n i))^2) atTop (𝓝 (T : ℝ)) := by
    simpa only [b, mesh_toNNReal, quadraticSum] using hQω
  obtain ⟨K₃, hK₃, h₃⟩ := hrω.third_bound
  have hr := mesh_family_remainder_tendsto
    (f := fun n i => F ω (mesh T n i)) (fun _ _ => hrω.smooth _) T.coe_nonneg
    hb.continuousOn hK₃ (fun _ _ x => h₃ _ x) hQ
  have hriem := mesh_riemann_tendsto T.coe_nonneg hrω.second_cont
  have htime := mesh_time_increment_tendsto (b := b) T.coe_nonneg hrω.time_cont
    hrω.time_deriv hrω.drift_cont
  let Q : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (2^n),
    iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
      (b (mesh T n (i+1))-b (mesh T n i))^2
  have hQweighted : Tendsto Q atTop
      (𝓝 (∫ t in (0 : ℝ)..(T : ℝ), iteratedDeriv 2 (F ω t) (b t))) := by
    have heq (n : ℕ) : Q n = dyadicQuadraticError B T C n ω +
        ∑ i ∈ Finset.range (2^n), iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
          ((T : ℝ) / (2 : ℝ)^n) := by
      simp only [Q, dyadicQuadraticError, C, b, mesh_toNNReal, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simpa only [b, ← heq, zero_add] using heω.add hriem
  have hTel (n : ℕ) : ∑ i ∈ Finset.range (2^n),
      (F ω (mesh T n (i+1)) (b (mesh T n (i+1))) -
        F ω (mesh T n i) (b (mesh T n i))) = F ω T (B T ω) - F ω 0 (B 0 ω) := by
    rw [Finset.sum_range_sub (fun i => F ω (mesh T n i) (b (mesh T n i))) (2^n)]
    simp only [mesh_zero, mesh_end, b, Real.toNNReal_coe, Real.toNNReal_zero]
  have hIdentity (n : ℕ) : fieldSum B T F n ω =
      F ω T (B T ω) - F ω 0 (B 0 ω) -
        (∑ i ∈ Finset.range (2^n),
          (F ω (mesh T n (i+1)) (b (mesh T n (i+1))) -
            F ω (mesh T n i) (b (mesh T n (i+1))))) - (1/2 : ℝ) * Q n -
        ∑ i ∈ Finset.range (2^n), remainder₂ (F ω (mesh T n i))
          (b (mesh T n i)) (b (mesh T n (i+1))) := by
    rw [← hTel n]
    simp only [Q, Finset.mul_sum, ← Finset.sum_sub_distrib]
    unfold fieldSum
    apply Finset.sum_congr rfl
    intro i hi
    simp only [remainder₂, iteratedDeriv_succ, iteratedDeriv_zero, b, mesh_toNNReal]
    ring
  have ht := (((tendsto_const_nhds (x := F ω T (B T ω) - F ω 0 (B 0 ω))).sub
    htime).sub (hQweighted.const_mul (1/2 : ℝ))).sub hr
  simpa only [b, ← hIdentity, sub_zero] using ht

end SLEExactGauge.BrownianField

namespace SLEExactGauge.BrownianField
open BrownianPredictable PredictableLimit TaylorMeshes TimeField BrownianIto

 

theorem field_ito_centered {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (F V : Ω → ℝ → ℝ → ℝ)
    (hreg : ∀ᵐ ω ∂P, FieldRegular (F ω) (V ω) (fun t => B t.toNNReal ω) T)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)]
      (fun ω => iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)))
    (hC2 : ∀ n i, MemLp
      (fun ω => iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)) 2 P)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hbound : ∀ n i, ∀ᵐ ω ∂P,
      |iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)| ≤ K₂)
    (hA : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)]
      (fun ω => deriv (F ω (mesh T n i)) (B (dyadicTime T n i) ω)))
    (hA2 : ∀ n i, MemLp
      (fun ω => deriv (F ω (mesh T n i)) (B (dyadicTime T n i) ω)) 2 P)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hAbound : ∀ n i, ∀ᵐ ω ∂P,
      |deriv (F ω (mesh T n i)) (B (dyadicTime T n i) ω)| ≤ K₁) :
    let Y := fun ω => F ω T (B T ω) - F ω 0 (B 0 ω) -
      (∫ t in (0 : ℝ)..(T : ℝ), V ω t (B t.toNNReal ω)) -
      (1/2 : ℝ) * ∫ t in (0 : ℝ)..(T : ℝ), iteratedDeriv 2 (F ω t) (B t.toNNReal ω)
    Integrable Y P ∧ (∫ ω, Y ω ∂P) = 0 := by
  dsimp only
  exact limit_centered hB T
    (fun n i ω => deriv (F ω (mesh T n i)) (B (dyadicTime T n i) ω))
    hA hA2 K₁ hK₁ hAbound _
    (fieldSum_tendsto hB T F V hreg hC hC2 K₂ hK₂ hbound)

end SLEExactGauge.BrownianField

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}

noncomputable def ClippedLogSolution.velocity
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (t : ℝ) (ω : Ω) : ℂ × ℝ :=
  clippedLogLoewnerField lo hi hle (Real.sqrt κ * B t.toNNReal ω) (c.Q t ω)

lemma ClippedLogSolution.velocity_continuous
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) :
    Continuous (fun t : ℝ => c.velocity t ω) := by
  have hb : Continuous (fun t : ℝ => Real.sqrt κ * B t.toNNReal ω) :=
    ((hBc ω).comp continuous_real_toNNReal).const_mul _
  have hc : Continuous (fun t => (Real.sqrt κ * B t.toNNReal ω, c.Q t ω)) :=
    hb.prodMk (c.lipschitz ω).continuous
  exact (continuous_clippedLogLoewnerField lo hi hle).comp
    (f := fun t : ℝ => (Real.sqrt κ * B t.toNNReal ω, c.Q t ω)) hc

lemma ClippedLogSolution.compact_field_regular
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (φ : (ℂ × ℝ) × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (T : ℝ≥0) (ω : Ω) :
    FieldRegular (fun t x => φ (c.Q t ω, x))
      (fun t x => fderiv ℝ φ (c.Q t ω, x) (c.velocity t ω, 0))
      (fun t => B t.toNNReal ω) T := by
  have hQc := (c.lipschitz ω).continuous
  have hVc := c.velocity_continuous hBc ω
  have hBb := (hBc ω).comp continuous_real_toNNReal
  have hDp := hφ.continuous_fderiv (by simp)
  obtain ⟨K, hK, _⟩ := compact_smooth_bounded_lipschitz (spatialPartial φ 3)
    (spatialPartial_smooth φ hφ 3) (spatialPartial_compact φ hφc 3)
  refine ⟨?_, ⟨K, K.coe_nonneg, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (hφ.comp (contDiff_const.prodMk contDiff_id)).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  · intro t x
    simpa only [← spatialPartial_eq_iteratedDeriv φ hφ, Real.norm_eq_abs] using hK (c.Q t ω, x)
  · intro x
    exact (hφ.continuous.comp (hQc.prodMk continuous_const)).continuousOn
  · intro t ht x
    have hd := (c.derivative ω t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
    exact ((hφ.differentiable (by simp)) (c.Q t ω, x)).hasFDerivAt.comp_hasDerivAt t
      (hd.prodMk (hasDerivAt_const t x))
  · exact ((hDp.comp ((hQc.comp continuous_fst).prodMk (hBb.comp continuous_snd))).clm_apply
      ((hVc.comp continuous_fst).prodMk continuous_const)).continuousOn
  · have hc := (spatialPartial_smooth φ hφ 2).continuous.comp (hQc.prodMk hBb)
    simpa only [Function.comp_def, spatialPartial_eq_iteratedDeriv φ hφ] using hc.continuousOn

lemma natural_eq_pastSigma (t : ℝ≥0) :
    Filtration.natural B (fun s => (hm s).stronglyMeasurable) t = pastSigma B t := by
  exact Filtration.natural_eq_comap B (fun s => (hm s).stronglyMeasurable) t

lemma mesh_eq_dyadicTime (T : ℝ≥0) (n i : ℕ) :
    mesh T n i = (dyadicTime T n i : ℝ) := by
  simp [mesh, dyadicTime]

lemma ClippedLogSolution.partial_adapted
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (φ : (ℂ × ℝ) × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (j : ℕ) (t : ℝ≥0) :
    Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) t]
      (fun ω => iteratedDeriv j (fun x => φ (c.Q t ω, x)) (B t ω)) := by
  simp_rw [← spatialPartial_eq_iteratedDeriv φ hφ]
  have hBa := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted
  exact (spatialPartial_smooth φ hφ j).continuous.measurable.comp
    ((c.adapted t).prodMk (hBa t))

 

theorem ClippedLogSolution.compact_field_ito
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (φ : (ℂ × ℝ) × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => fieldSum B T (fun ω t x => φ (c.Q t ω, x)) n ω) atTop
      (𝓝 (φ (c.Q T ω, B T ω) - φ (c.Q 0 ω, B 0 ω) -
        (∫ t in (0 : ℝ)..(T : ℝ), fderiv ℝ φ (c.Q t ω, B t.toNNReal ω) (c.velocity t ω, 0)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(T : ℝ),
          iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t.toNNReal ω))) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨K, hK, _⟩ := compact_smooth_bounded_lipschitz (spatialPartial φ 2)
    (spatialPartial_smooth φ hφ 2) (spatialPartial_compact φ hφc 2)
  have hb (t : ℝ≥0) (ω : Ω) :
      |iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t ω)| ≤ K := by
    simpa only [← spatialPartial_eq_iteratedDeriv φ hφ, Real.norm_eq_abs] using hK (c.Q t ω, B t ω)
  have hma (t : ℝ≥0) := c.partial_adapted φ hφ 2 t
  have hp (t : ℝ≥0) : MemLp
      (fun ω => iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t ω)) 2 P := by
    exact MemLp.of_bound ((hma t).mono (Filtration.le _ _) le_rfl).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb t ω)
  apply fieldSum_tendsto hB T (fun ω t x => φ (c.Q t ω, x))
    (fun ω t x => fderiv ℝ φ (c.Q t ω, x) (c.velocity t ω, 0))
    (Eventually.of_forall (c.compact_field_regular hBc φ hφ hφc T))
    (fun n i => ?_) (fun n i => ?_) K K.coe_nonneg (fun n i => ?_)
  · have hx := (hma (dyadicTime T n i)).mono
      (le_of_eq (natural_eq_pastSigma (B := B) (hm := hm) (dyadicTime T n i))) le_rfl
    simpa only [mesh_eq_dyadicTime] using hx
  · simpa only [mesh_eq_dyadicTime] using hp (dyadicTime T n i)
  · exact Eventually.of_forall fun ω => by
      simpa only [mesh_eq_dyadicTime] using hb (dyadicTime T n i) ω

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes TimeField

lemma prefix_const_sum_le {T ζ : ℝ} (hT : 0 ≤ T) (hζ : 0 ≤ ζ)
    (k n : ℕ) (hk : k ≤ 2^n) :
    (∑ _i ∈ Finset.range k, ζ * (T / (2 : ℝ)^n)) ≤ ζ * T := by
  calc
    _ ≤ ∑ _i ∈ Finset.range (2^n), ζ * (T / (2 : ℝ)^n) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun _ _ _ => by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

lemma mesh_prefix_riemann_error {h : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hh : ContinuousOn h (Icc 0 T)) (k : ℕ → ℕ) (hk : ∀ n, k n ≤ 2^n) :
    Tendsto (fun n => (∑ i ∈ Finset.range (k n),
      h (mesh T n i) * (T / (2 : ℝ)^n)) - ∫ t in (0 : ℝ)..mesh T n (k n), h t) atTop (𝓝 0) := by
  have hint (n i : ℕ) (hi : i < 2^n) :
      IntervalIntegrable h volume (mesh T n i) (mesh T n (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (mesh_mono T hT n (Nat.le_succ i))]
    apply hh.mono
    exact Icc_subset_Icc (mesh_mem T hT n i hi.le).1
      (mesh_mem T hT n (i+1) hi).2
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hh
  apply Metric.tendsto_atTop.2
  intro ε hε
  let ζ : ℝ := ε / (T+1)
  have hζ : 0 < ζ := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 hu ζ hζ
  have hn := (mesh_step_tendsto T).eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hn
  refine ⟨N, fun n hn => ?_⟩
  have hnδ := hN n hn
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (fun i hi => hint n i (hi.trans_le (hk n)))
  rw [mesh_zero] at hsum
  have heach (i : ℕ) (hi : i < 2^n) :
      |h (mesh T n i) * (T / (2 : ℝ)^n) -
        ∫ t in mesh T n i..mesh T n (i+1), h t| ≤ ζ * (T / (2 : ℝ)^n) := by
    have heq : h (mesh T n i) * (T / (2 : ℝ)^n) =
        ∫ _ : ℝ in mesh T n i..mesh T n (i+1), h (mesh T n i) := by
      rw [intervalIntegral.integral_const, mesh_step, smul_eq_mul, mul_comm]
    rw [heq, ← intervalIntegral.integral_sub intervalIntegrable_const (hint n i hi)]
    have hbound : ∀ t ∈ uIoc (mesh T n i) (mesh T n (i+1)),
        ‖h (mesh T n i) - h t‖ ≤ ζ := by
      intro t ht
      rw [uIoc_of_le (mesh_mono T hT n (Nat.le_succ i))] at ht
      have htT : t ∈ Icc 0 T := ⟨(mesh_mem T hT n i hi.le).1.trans ht.1.le,
        ht.2.trans (mesh_mem T hT n (i+1) hi).2⟩
      have hdist : dist (mesh T n i) t < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 ht.1.le)]
        have hstep := mesh_step T n i
        have ht' : t ≤ mesh T n (i+1) := ht.2
        linarith
      simpa only [Real.norm_eq_abs, Real.dist_eq] using
        (hmod _ (mesh_mem T hT n i hi.le) _ htT hdist).le
    have hbound' := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, mesh_step, abs_of_nonneg (div_nonneg hT (by positivity))] at hbound'
    exact hbound'
  rw [Real.dist_eq, sub_zero, ← hsum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range (k n),
        |h (mesh T n i) * (T / (2 : ℝ)^n) -
          ∫ t in mesh T n i..mesh T n (i+1), h t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (k n), ζ * (T / (2 : ℝ)^n) :=
      Finset.sum_le_sum (fun i hi => heach i ((Finset.mem_range.1 hi).trans_le (hk n)))
    _ ≤ ζ * T := prefix_const_sum_le hT hζ.le (k n) n (hk n)
    _ < ε := by
      dsimp [ζ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < T+1)]
      nlinarith

lemma mesh_prefix_riemann_tendsto {h : ℝ → ℝ} {T S : ℝ}
    (hT : 0 ≤ T) (hh : ContinuousOn h (Icc 0 T))
    (k : ℕ → ℕ) (hk : ∀ n, k n ≤ 2^n) (hS : S ∈ Icc 0 T)
    (hlim : Tendsto (fun n => mesh T n (k n)) atTop (𝓝 S)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (k n),
      h (mesh T n i) * (T / (2 : ℝ)^n)) atTop (𝓝 (∫ t in (0 : ℝ)..S, h t)) := by
  have hint : IntegrableOn h (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    exact hh.integrableOn_Icc
  have hc := intervalIntegral.continuousOn_primitive_interval hint
  rw [uIcc_of_le hT] at hc
  have hi := (hc S hS).tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Eventually.of_forall fun n => mesh_mem T hT n (k n) (hk n)⟩)
  have he := (mesh_prefix_riemann_error hT hh k hk).add hi
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using he

lemma mesh_prefix_remainder_tendsto {f : ℕ → ℕ → ℝ → ℝ} {b : ℝ → ℝ}
    (hf : ∀ n i, ContDiff ℝ 3 (f n i))
    {T V K : ℝ} (hT : 0 ≤ T) (hb : ContinuousOn b (Icc 0 T)) (hK : 0 ≤ K)
    (h3 : ∀ n i x, |iteratedDeriv 3 (f n i) x| ≤ K)
    (k : ℕ → ℕ) (hk : ∀ n, k n ≤ 2^n)
    (hQ : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1)) - b (mesh T n i))^2) atTop (𝓝 V)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (k n),
      remainder₂ (f n i) (b (mesh T n i)) (b (mesh T n (i+1)))) atTop (𝓝 0) := by
  have hV : 0 ≤ V := ge_of_tendsto hQ (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ := ε / ((K+1)*(V+1))
  have hδ : 0 < δ := div_pos hε (mul_pos (by linarith) (by linarith))
  have hs := mesh_increments_small hT hb hδ
  have hq := hQ.eventually (gt_mem_nhds (show V < V+1 by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.and hq)
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨hs, hq⟩
  have hr := sum_family_remainder₂_bound (hf n) (fun i => b (mesh T n i)) (k n) K δ hK hδ.le
    (fun i _ z _ => h3 n i z) (fun i hi => (hs i (hi.trans_le (hk n))).le)
  simp only [Real.dist_eq, sub_zero]
  calc
    _ ≤ K * δ / 6 * ∑ i ∈ Finset.range (k n),
        (b (mesh T n (i+1)) - b (mesh T n i))^2 := hr
    _ ≤ K * δ / 6 * ∑ i ∈ Finset.range (2^n),
        (b (mesh T n (i+1)) - b (mesh T n i))^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (hk n))
        (fun i _ _ => sq_nonneg _)
    _ ≤ K * δ / 6 * (V+1) := mul_le_mul_of_nonneg_left hq.le (by positivity)
    _ < ε := by
      dsimp [δ]
      have hden : 0 < (K+1)*(V+1) := mul_pos (by linarith) (by linarith)
      have hid : K * (ε / ((K+1)*(V+1))) / 6 * (V+1) = ε * (K / (6*(K+1))) := by
        field_simp
      rw [hid]
      have hk : K / (6*(K+1)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      simpa using mul_lt_mul_of_pos_left hk hε

lemma mesh_prefix_time_increment_tendsto {F V : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T S : ℝ}
    (hT : 0 ≤ T)
    (hF : ∀ x, ContinuousOn (fun t => F t x) (Icc 0 T))
    (hD : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun u => F u x) (V t x) t)
    (hV : ContinuousOn (fun p : ℝ × ℝ => V p.1 (b p.2)) ((Icc 0 T) ×ˢ (Icc 0 T)))
    (k : ℕ → ℕ) (hk : ∀ n, k n ≤ 2^n) (hS : S ∈ Icc 0 T)
    (hlim : Tendsto (fun n => mesh T n (k n)) atTop (𝓝 S)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (k n),
      (F (mesh T n (i+1)) (b (mesh T n (i+1))) -
        F (mesh T n i) (b (mesh T n (i+1))))) atTop
      (𝓝 (∫ t in (0 : ℝ)..S, V t (b t))) := by
  rcases hT.eq_or_lt with hT | hT
  · subst T
    have : S = 0 := le_antisymm hS.2 hS.1
    subst S
    simp [mesh]
  have hVc : ContinuousOn (fun t => V t (b t)) (Icc 0 T) :=
    hV.comp (continuousOn_id.prodMk continuousOn_id) (fun t ht => ⟨ht, ht⟩)
  have hriem := mesh_prefix_riemann_tendsto hT.le hVc k hk hS hlim
  have herror : Tendsto (fun n => ∑ i ∈ Finset.range (k n),
      (F (mesh T n (i+1)) (b (mesh T n (i+1))) -
        F (mesh T n i) (b (mesh T n (i+1))) -
          V (mesh T n i) (b (mesh T n i)) * (T / (2 : ℝ)^n))) atTop (𝓝 0) := by
    have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hV
    apply Metric.tendsto_atTop.2
    intro ε hε
    let ζ : ℝ := ε / (T+1)
    have hζ : 0 < ζ := div_pos hε (by linarith)
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 hu ζ hζ
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((mesh_step_tendsto T).eventually (gt_mem_nhds hδ))
    refine ⟨N, fun n hn => ?_⟩
    have hnδ := hN n hn
    have heach (i : ℕ) (hi : i < 2^n) :
        |F (mesh T n (i+1)) (b (mesh T n (i+1))) -
          F (mesh T n i) (b (mesh T n (i+1))) -
            V (mesh T n i) (b (mesh T n i)) * (T / (2 : ℝ)^n)| ≤
        ζ * (T / (2 : ℝ)^n) := by
      have hstep_pos : mesh T n i < mesh T n (i+1) := by
        have : 0 < mesh T n (i+1) - mesh T n i := by rw [mesh_step]; positivity
        linarith
      have hleft := mesh_mem T hT.le n i hi.le
      have hright := mesh_mem T hT.le n (i+1) hi
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
        (fun t => F t (b (mesh T n (i+1)))) (fun t => V t (b (mesh T n (i+1))))
        hstep_pos ((hF _).mono (Icc_subset_Icc hleft.1 hright.2))
        (fun t ht => hD t ⟨hleft.1.trans_lt ht.1, ht.2.trans_le hright.2⟩ _)
      have hcT : c ∈ Icc 0 T := ⟨hleft.1.trans hc.1.le, hc.2.le.trans hright.2⟩
      have hdist : dist (c, mesh T n (i+1)) (mesh T n i, mesh T n i) < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        constructor
        · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hc.1.le)]
          have hcs := hc.2
          have hstep := mesh_step T n i
          linarith
        · rw [Real.dist_eq, mesh_step, abs_of_nonneg (by positivity)]
          exact hnδ
      have hvmod := (hmod (c, mesh T n (i+1)) ⟨hcT, hright⟩
        (mesh T n i, mesh T n i) ⟨hleft, hleft⟩ hdist).le
      simp only [Real.dist_eq] at hvmod
      have hid : F (mesh T n (i+1)) (b (mesh T n (i+1))) -
          F (mesh T n i) (b (mesh T n (i+1))) =
          V c (b (mesh T n (i+1))) * (T / (2 : ℝ)^n) := by
        rw [mesh_step] at heq
        exact (eq_div_iff (ne_of_gt (div_pos hT (by positivity)))).1 heq |>.symm
      rw [hid, ← sub_mul, abs_mul, abs_of_nonneg (show 0 ≤ T / (2 : ℝ)^n by positivity)]
      exact mul_le_mul_of_nonneg_right hvmod (by positivity)
    rw [Real.dist_eq, sub_zero]
    calc
      _ ≤ ∑ i ∈ Finset.range (k n),
          |F (mesh T n (i+1)) (b (mesh T n (i+1))) -
            F (mesh T n i) (b (mesh T n (i+1))) -
              V (mesh T n i) (b (mesh T n i)) * (T / (2 : ℝ)^n)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (k n), ζ * (T / (2 : ℝ)^n) :=
        Finset.sum_le_sum (fun i hi => heach i ((Finset.mem_range.1 hi).trans_le (hk n)))
      _ ≤ ζ * T := prefix_const_sum_le hT.le hζ.le (k n) n (hk n)
      _ < ε := by
        dsimp [ζ]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < T+1)]
        nlinarith
  have hadd := herror.add hriem
  simp only [Finset.sum_sub_distrib, sub_add_cancel, zero_add] at hadd
  simpa only [Finset.sum_sub_distrib] using hadd

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianIto TaylorMeshes

noncomputable def stoppedDyadicIndex (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) : ℕ :=
  Nat.ceil (t / (T / (2 : ℝ≥0)^n))

lemma lt_stoppedDyadicIndex {T : ℝ≥0} (hT : 0 < T) (n i : ℕ) (t : ℝ≥0) :
    i < stoppedDyadicIndex T n t ↔ dyadicTime T n i < t := by
  have hd : 0 < T / (2 : ℝ≥0)^n := by positivity
  simp only [stoppedDyadicIndex, Nat.lt_ceil, lt_div_iff₀ hd, dyadicTime]

lemma stoppedDyadicIndex_le {T : ℝ≥0} (hT : 0 < T) (n : ℕ)
    {t : ℝ≥0} (ht : t ≤ T) : stoppedDyadicIndex T n t ≤ 2^n := by
  rw [stoppedDyadicIndex, Nat.ceil_le, div_le_iff₀ (by positivity : 0 < T / (2 : ℝ≥0)^n)]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel₀ _ (pow_ne_zero n (by norm_num : (2 : ℝ≥0) ≠ 0))] using ht

end SLEExactGauge
end
end
end
end
end

end OAI
