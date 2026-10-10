import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.StochasticCalculus

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
namespace ExactSLEGenerator
lemma riemann_sum_tendsto (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n+1),
      (T / (n+1 : ℕ)) * f ((i : ℝ)*(T / (n+1 : ℕ)))) atTop
      (𝓝 (∫ s in 0..T, f s)) := by
  by_cases hT0 : T = 0
  · subst T
    simp
  have hTp : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
  have hu := (isCompact_Icc : IsCompact (Set.Icc 0 T)).uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  have hmesh : Tendsto (fun n : ℕ => T / (n+1 : ℕ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (n+1 : ℕ)) atTop atTop :=
      tendsto_add_atTop_nat 1
    simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hh)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, huδ⟩ := hu (ε/(2*T)) (by positivity)
  filter_upwards [hmesh.eventually_lt_const hδ] with n hn
  rw [Real.dist_eq]
  have he := riemann_sum_error_le f hf T hT (n+1) (Nat.succ_pos _) (ε/(2*T))
    (by positivity) (by
      intro u hu v hv huv
      exact le_of_lt (huδ u hu v hv (by simpa only [Real.dist_eq] using huv.trans_lt hn)))
  calc
    _ ≤ ε / (2*T) * T := he
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

lemma riemann_sum_bound (f : ℝ → ℝ) (T K : ℝ) (hT : 0 ≤ T) (N : ℕ) (hN : 0 < N)
    (hbound : ∀ t ∈ Set.Icc 0 T, |f t| ≤ K) :
    |∑ i ∈ Finset.range N, (T/N)*f ((i : ℝ)*(T/N))| ≤ K*T := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh : 0 ≤ T / N := div_nonneg hT hNr.le
  have hNh : (N : ℝ) * (T / N) = T := by field_simp
  calc
    _ ≤ ∑ i ∈ Finset.range N, |(T/N)*f ((i : ℝ)*(T/N))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, (T/N)*K := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg hh]
      apply mul_le_mul_of_nonneg_left _ hh
      apply hbound
      refine ⟨by positivity, ?_⟩
      calc
        _ ≤ (N : ℝ)*(T/N) := mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Finset.mem_range.mp hi).le) hh
        _ = T := hNh
    _ = K*((N : ℝ)*(T/N)) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ = K*T := by rw [hNh]

lemma expected_riemann_sum_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (W : Measure Ω) [IsFiniteMeasure W] (f : ℝ → Ω → ℝ)
    (hf : ∀ b, Continuous (fun t => f t b))
    (hm : ∀ t, AEStronglyMeasurable (f t) W)
    (T K : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ b t, t ∈ Set.Icc 0 T → |f t b| ≤ K) :
    Tendsto (fun n : ℕ => ∫ b, ∑ i ∈ Finset.range (n+1),
      (T/(n+1 : ℕ))*f ((i : ℝ)*(T/(n+1 : ℕ))) b ∂W) atTop
      (𝓝 (∫ b, (∫ t in 0..T, f t b) ∂W)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => K*T)
  · intro n
    have hs := Finset.aestronglyMeasurable_sum
      (Finset.range (n+1)) (fun i hi =>
        (hm ((i : ℝ)*(T/(n+1 : ℕ)))).const_mul (T/(n+1 : ℕ)))
    convert hs using 1
    funext b
    simp only [Finset.sum_apply]
  · exact integrable_const _
  · intro n
    refine ae_of_all W ?_
    intro b
    simpa only [Real.norm_eq_abs] using
      riemann_sum_bound (fun t => f t b) T K hT (n+1) (Nat.succ_pos _) (hbound b)
  · exact ae_of_all W (fun b => riemann_sum_tendsto (fun t => f t b) (hf b) T hT)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma stieltjes_riemann_error_le (D : ℝ → E →L[ℝ] ℝ) (a : ℝ → E)
    (ha : Continuous a) (T M ε : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (N : ℕ) (hN : 0 < N)
    (hbound : ∀ t ∈ Set.Icc 0 T, ‖D t‖ ≤ M)
    (hmod : ∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T,
      |u-v| ≤ T/N → ‖a u-a v‖ ≤ ε) :
    |(∑ i ∈ Finset.range N, D ((i : ℝ)*(T/N))
        (∫ s in (i : ℝ)*(T/N)..((i+1 : ℕ) : ℝ)*(T/N), a s)) -
      ∑ i ∈ Finset.range N, (T/N) * D ((i : ℝ)*(T/N)) (a ((i : ℝ)*(T/N)))| ≤ M*ε*T := by
  let h := T / (N : ℝ)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh : 0 ≤ h := div_nonneg hT hNr.le
  have hNh : (N : ℝ) * h = T := by dsimp [h]; field_simp
  have hdiff (i : ℕ) : ((i+1 : ℕ) : ℝ)*h-(i : ℝ)*h = h := by push_cast; ring
  have he (i : ℕ) (hi : i < N) :
      |D ((i : ℝ)*h) (∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h, a s) -
        h * D ((i : ℝ)*h) (a ((i : ℝ)*h))| ≤ M*ε*h := by
    have hai : (i : ℝ)*h ∈ Set.Icc 0 T := by
      refine ⟨by positivity, ?_⟩
      rw [← hNh]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hh
    have hbi : ((i+1 : ℕ) : ℝ)*h ∈ Set.Icc 0 T := by
      refine ⟨by positivity, ?_⟩
      rw [← hNh]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh
    have hab : (i : ℝ)*h ≤ ((i+1 : ℕ) : ℝ)*h := by linarith [hdiff i]
    have hpt : ∀ s ∈ Set.uIoc ((i : ℝ)*h) (((i+1 : ℕ) : ℝ)*h),
        ‖D ((i : ℝ)*h) (a s-a ((i : ℝ)*h))‖ ≤ M*ε := by
      intro s hs
      rw [Set.uIoc_of_le hab] at hs
      have has : ‖a s - a ((i : ℝ)*h)‖ ≤ ε := by
        apply hmod s ⟨hai.1.trans hs.1.le, hs.2.trans hbi.2⟩ _ hai
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1.le)]
        linarith [hs.2, hdiff i]
      calc
        _ ≤ ‖D ((i : ℝ)*h)‖ * ‖a s-a ((i : ℝ)*h)‖ := (D _).le_opNorm _
        _ ≤ M * ‖a s-a ((i : ℝ)*h)‖ := mul_le_mul_of_nonneg_right (hbound _ hai) (norm_nonneg _)
        _ ≤ M*ε := mul_le_mul_of_nonneg_left has hM
    have hi₁ := ((D ((i : ℝ)*h)).continuous.comp ha).intervalIntegrable
      (μ := volume) ((i : ℝ)*h) (((i+1 : ℕ) : ℝ)*h)
    simp only [Function.comp_def] at hi₁
    have hi₂ : IntervalIntegrable (fun _ : ℝ => D ((i : ℝ)*h) (a ((i : ℝ)*h))) volume
        ((i : ℝ)*h) (((i+1 : ℕ) : ℝ)*h) := intervalIntegrable_const
    have hval : (∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h,
        D ((i : ℝ)*h) (a s-a ((i : ℝ)*h))) =
        D ((i : ℝ)*h) (∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h, a s) -
          h * D ((i : ℝ)*h) (a ((i : ℝ)*h)) := by
      simp only [map_sub]
      rw [intervalIntegral.integral_sub hi₁ hi₂,
        (D _).intervalIntegral_comp_comm (ha.intervalIntegrable _ _),
        intervalIntegral.integral_const, hdiff, smul_eq_mul]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [hval, Real.norm_eq_abs, hdiff, abs_of_nonneg hh] at hb
    exact hb
  change |(∑ i ∈ Finset.range N, D ((i : ℝ)*h)
    (∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h, a s)) -
      ∑ i ∈ Finset.range N, h*D ((i : ℝ)*h) (a ((i : ℝ)*h))| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range N, |D ((i : ℝ)*h)
        (∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h, a s) -
          h*D ((i : ℝ)*h) (a ((i : ℝ)*h))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, M*ε*h := Finset.sum_le_sum fun i hi => he i (Finset.mem_range.mp hi)
    _ = M*ε*((N : ℝ)*h) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ = M*ε*T := by rw [hNh]

lemma stieltjes_sum_tendsto (D : ℝ → E →L[ℝ] ℝ) (a : ℝ → E)
    (hD : Continuous D) (ha : Continuous a) (T M : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Set.Icc 0 T, ‖D t‖ ≤ M) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n+1), D ((i : ℝ)*(T/(n+1 : ℕ)))
      (∫ s in (i : ℝ)*(T/(n+1 : ℕ))..((i+1 : ℕ) : ℝ)*(T/(n+1 : ℕ)), a s)) atTop
      (𝓝 (∫ t in 0..T, D t (a t))) := by
  let S := fun n : ℕ => ∑ i ∈ Finset.range (n+1), D ((i : ℝ)*(T/(n+1 : ℕ)))
    (∫ s in (i : ℝ)*(T/(n+1 : ℕ))..((i+1 : ℕ) : ℝ)*(T/(n+1 : ℕ)), a s)
  let R := fun n : ℕ => ∑ i ∈ Finset.range (n+1), (T/(n+1 : ℕ)) *
    D ((i : ℝ)*(T/(n+1 : ℕ))) (a ((i : ℝ)*(T/(n+1 : ℕ))))
  have hR : Tendsto R atTop (𝓝 (∫ t in 0..T, D t (a t))) :=
    riemann_sum_tendsto (fun t => D t (a t)) (hD.clm_apply ha) T hT
  have hdiff : Tendsto (fun n => S n-R n) atTop (𝓝 0) := by
    have hu := (isCompact_Icc : IsCompact (Set.Icc 0 T)).uniformContinuousOn_of_continuous ha.continuousOn
    rw [Metric.uniformContinuousOn_iff] at hu
    have hmesh : Tendsto (fun n : ℕ => T/(n+1 : ℕ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hh : 0 < M*T+1 := by positivity
    have hep : 0 < ε / (2*(M*T+1)) := by positivity
    obtain ⟨δ, hδ, huδ⟩ := hu (ε/(2*(M*T+1))) hep
    filter_upwards [hmesh.eventually_lt_const hδ] with n hn
    have herror := stieltjes_riemann_error_le D a ha T M (ε/(2*(M*T+1))) hT hM
      (n+1) (Nat.succ_pos _) hbound (by
        intro u hu v hv huv
        have hub := huδ u hu v hv (by simpa only [Real.dist_eq] using huv.trans_lt hn)
        exact le_of_lt (by simpa only [dist_eq_norm] using hub))
    rw [Real.dist_eq, sub_zero]
    change |S n-R n| ≤ _ at herror
    calc
      _ ≤ M*(ε/(2*(M*T+1)))*T := herror
      _ ≤ (ε/(2*(M*T+1)))*(M*T+1) := by nlinarith [hep.le]
      _ = ε/2 := by field_simp
      _ < ε := by linarith
  have hh := hdiff.add hR
  simpa only [sub_add_cancel, zero_add] using hh

omit [CompleteSpace E] in
lemma stieltjes_sum_bound (D : ℝ → E →L[ℝ] ℝ) (a : ℝ → E)
    (T M K : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M) (_hK : 0 ≤ K)
    (N : ℕ) (hN : 0 < N)
    (hD : ∀ t ∈ Set.Icc 0 T, ‖D t‖ ≤ M)
    (ha : ∀ t ∈ Set.Icc 0 T, ‖a t‖ ≤ K) :
    |∑ i ∈ Finset.range N, D ((i : ℝ)*(T/N))
      (∫ s in (i : ℝ)*(T/N)..((i+1 : ℕ) : ℝ)*(T/N), a s)| ≤ M*K*T := by
  let h := T / (N : ℝ)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh : 0 ≤ h := div_nonneg hT hNr.le
  have hNh : (N : ℝ) * h = T := by dsimp [h]; field_simp
  have hdiff (i : ℕ) : ((i+1 : ℕ) : ℝ)*h-(i : ℝ)*h = h := by push_cast; ring
  have he (i : ℕ) (hi : i < N) :
      |D ((i : ℝ)*h) (∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h, a s)| ≤ M*K*h := by
    have hai : (i : ℝ)*h ∈ Set.Icc 0 T := by
      refine ⟨by positivity, ?_⟩
      rw [← hNh]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hh
    have hbi : ((i+1 : ℕ) : ℝ)*h ∈ Set.Icc 0 T := by
      refine ⟨by positivity, ?_⟩
      rw [← hNh]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh
    have hab : (i : ℝ)*h ≤ ((i+1 : ℕ) : ℝ)*h := by linarith [hdiff i]
    have hv : ‖∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h, a s‖ ≤ K*h := by
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs =>
        ha s (show s ∈ Set.Icc 0 T from by
          rw [Set.uIoc_of_le hab] at hs
          exact ⟨hai.1.trans hs.1.le, hs.2.trans hbi.2⟩))
      simpa only [hdiff, abs_of_nonneg hh] using hb
    calc
      _ ≤ ‖D ((i : ℝ)*h)‖ * ‖∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h, a s‖ := by
        simpa only [Real.norm_eq_abs] using (D ((i : ℝ)*h)).le_opNorm _
      _ ≤ M * (K*h) := mul_le_mul (hD _ hai) hv (norm_nonneg _) hM
      _ = _ := by ring
  change |∑ i ∈ Finset.range N, D ((i : ℝ)*h)
    (∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h, a s)| ≤ _
  calc
    _ ≤ ∑ i ∈ Finset.range N, |D ((i : ℝ)*h)
        (∫ s in (i : ℝ)*h..((i+1 : ℕ) : ℝ)*h, a s)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, M*K*h := Finset.sum_le_sum fun i hi => he i (Finset.mem_range.mp hi)
    _ = M*K*((N : ℝ)*h) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ = M*K*T := by rw [hNh]

lemma expected_stieltjes_sum_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (W : Measure Ω) [IsFiniteMeasure W] (D : ℝ → Ω → E →L[ℝ] ℝ) (a : ℝ → Ω → E)
    (hD : ∀ b, Continuous (fun t => D t b)) (ha : ∀ b, Continuous (fun t => a t b))
    (hm : ∀ u v, AEStronglyMeasurable (fun b => D u b (∫ s in u..v, a s b)) W)
    (T M K : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hDb : ∀ b t, t ∈ Set.Icc 0 T → ‖D t b‖ ≤ M)
    (hab : ∀ b t, t ∈ Set.Icc 0 T → ‖a t b‖ ≤ K) :
    Tendsto (fun n : ℕ => ∫ b, ∑ i ∈ Finset.range (n+1), D ((i : ℝ)*(T/(n+1 : ℕ))) b
      (∫ s in (i : ℝ)*(T/(n+1 : ℕ))..((i+1 : ℕ) : ℝ)*(T/(n+1 : ℕ)), a s b) ∂W) atTop
      (𝓝 (∫ b, (∫ t in 0..T, D t b (a t b)) ∂W)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => M*K*T)
  · intro n
    have hs := Finset.aestronglyMeasurable_sum (Finset.range (n+1)) (fun i hi =>
      hm ((i : ℝ)*(T/(n+1 : ℕ))) (((i+1 : ℕ) : ℝ)*(T/(n+1 : ℕ))))
    convert hs using 1
    funext b
    simp only [Finset.sum_apply]
  · exact integrable_const _
  · intro n
    refine ae_of_all W ?_
    intro b
    simpa only [Real.norm_eq_abs] using stieltjes_sum_bound (fun t => D t b)
      (fun t => a t b) T M K hT hM hK (n+1) (Nat.succ_pos _) (hDb b) (hab b)
  · exact ae_of_all W (fun b => stieltjes_sum_tendsto (fun t => D t b)
      (fun t => a t b) (hD b) (ha b) T M hT hM (hDb b))

end ExactSLEGenerator

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace ExactSLEGenerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 

theorem dynkin_of_mixed_taylor (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (start : ℝ≥0) (F Z Y : ℝ → Driver → ℝ) (D : ℝ → Driver → E →L[ℝ] ℝ) (A : ℝ → Driver → E)
    (hF : ∀ t : ℝ≥0, Integrable (F t) W)
    (hZm : ∀ t : ℝ≥0, Measurable[rawFiltration (start+t)] (Z t))
    (hYm : ∀ t : ℝ≥0, Measurable[rawFiltration (start+t)] (Y t))
    (hZi : ∀ t : ℝ≥0, Integrable (Z t) W)
    (hYc : ∀ b, Continuous (fun t => Y t b))
    (hYm' : ∀ t, AEStronglyMeasurable (Y t) W)
    (hDc : ∀ b, Continuous (fun t => D t b))
    (hAc : ∀ b, Continuous (fun t => A t b))
    (hVm : ∀ u v, AEStronglyMeasurable (fun b => D u b (∫ t in u..v, A t b)) W)
    (C M K : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hYb : ∀ b t, |Y t b| ≤ M) (hDb : ∀ b t, ‖D t b‖ ≤ M)
    (hAb : ∀ b t, ‖A t b‖ ≤ K)
    (hTaylor : ∀ (s h : ℝ≥0) b,
      |F (s+h) b - F s b - Z s b * increment (start+s) h b -
        Y s b * increment (start+s) h b ^ 2 / 2 - D s b (∫ t in (s : ℝ)..(s+h : ℝ≥0), A t b)| ≤
      C * (K * h * (|increment (start+s) h b| + K * h) + |increment (start+s) h b| ^ 3))
    (T : ℝ≥0) :
    (∫ b, F T b ∂W) - (∫ b, F 0 b ∂W) =
      (1/2 : ℝ) * (∫ b, (∫ t in 0..(T : ℝ), Y t b) ∂W) +
      (∫ b, (∫ t in 0..(T : ℝ), D t b (A t b)) ∂W) := by
  have hYi (t : ℝ) : Integrable (Y t) W :=
    Integrable.of_bound (hYm' t) M (ae_of_all W (fun b => by simpa [Real.norm_eq_abs] using hYb b t))
  have hVi (u v : ℝ) : Integrable (fun b => D u b (∫ t in u..v, A t b)) W := by
    apply Integrable.of_bound (hVm u v) (M * (K * |v-u|))
    refine ae_of_all W (fun b => ?_)
    calc
      _ ≤ ‖D u b‖ * ‖∫ t in u..v, A t b‖ := (D u b).le_opNorm _
      _ ≤ M * (K * |v-u|) := mul_le_mul (hDb b u)
        (intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => hAb b t))
        (norm_nonneg _) hM
  let S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n+1),
    ((T : ℝ)/(n+1 : ℕ)/2 * (∫ b, Y ((i : ℝ)*((T : ℝ)/(n+1 : ℕ))) b ∂W) +
      (∫ b, D ((i : ℝ)*((T : ℝ)/(n+1 : ℕ))) b
        (∫ t in ((i : ℝ)*((T : ℝ)/(n+1 : ℕ)))..(((i+1 : ℕ) : ℝ)*((T : ℝ)/(n+1 : ℕ))), A t b) ∂W))
  have hS (n : ℕ) : S n =
      (1/2 : ℝ) * (∫ b, ∑ i ∈ Finset.range (n+1),
        ((T : ℝ)/(n+1 : ℕ))*Y ((i : ℝ)*((T : ℝ)/(n+1 : ℕ))) b ∂W) +
      (∫ b, ∑ i ∈ Finset.range (n+1), D ((i : ℝ)*((T : ℝ)/(n+1 : ℕ))) b
        (∫ t in ((i : ℝ)*((T : ℝ)/(n+1 : ℕ)))..(((i+1 : ℕ) : ℝ)*((T : ℝ)/(n+1 : ℕ))), A t b) ∂W) := by
    rw [integral_finsetSum _ (fun i hi => (hYi _).const_mul _),
      integral_finsetSum _ (fun i hi => hVi _ _)]
    simp only [integral_const_mul, Finset.mul_sum]
    dsimp [S]
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hlim : Tendsto S atTop (𝓝 ((1/2 : ℝ) * (∫ b, (∫ t in 0..(T : ℝ), Y t b) ∂W) +
      (∫ b, (∫ t in 0..(T : ℝ), D t b (A t b)) ∂W))) := by
    have hy := expected_riemann_sum_tendsto W Y hYc hYm' T M T.coe_nonneg
      (fun b t ht => hYb b t)
    have hv := expected_stieltjes_sum_tendsto W D A hDc hAc hVm T M K T.coe_nonneg hM hK
      (fun b t ht => hDb b t) (fun b t ht => hAb b t)
    convert (hy.const_mul (1/2 : ℝ)).add hv using 1
    funext n
    exact hS n
  have herr (n : ℕ) : |(∫ b, F T b ∂W) - (∫ b, F 0 b ∂W) - S n| ≤
      C * (T : ℝ) * ((K * absMoment 1 + absMoment 3) *
        Real.sqrt ((T : ℝ)/(n+1 : ℕ)) + K^2*((T : ℝ)/(n+1 : ℕ))) := by
    let h : ℝ≥0 := T / (n+1 : ℕ)
    have hnh : ((n+1 : ℕ) : ℝ≥0) * h = T := by dsimp [h]; field_simp
    have he := expected_taylor_sum W hW start (n+1) h
      (fun i => F (((i : ℝ≥0)*h : ℝ≥0) : ℝ)) (fun i => Z (((i : ℝ≥0)*h : ℝ≥0) : ℝ)) (fun i => Y (((i : ℝ≥0)*h : ℝ≥0) : ℝ))
      (fun i b => D (((i : ℝ≥0)*h : ℝ≥0) : ℝ) b (∫ t in (((i : ℝ≥0)*h) : ℝ)..((((i+1 : ℕ) : ℝ≥0)*h) : ℝ), A t b))
      (fun i => hF _) (fun i => hVi _ _) (fun i => hZm _) (fun i => hYm _)
      (fun i => hZi _) (fun i => hYi _) C K hC hK (by
        intro i hi b
        have ht := hTaylor ((i : ℝ≥0)*h) h b
        convert ht using 1; push_cast; ring_nf)
    have hnr : ((n+1 : ℕ) : ℝ) * (h : ℝ) = T := by exact_mod_cast hnh
    simp only [hnh, Nat.cast_zero, zero_mul, NNReal.coe_zero] at he
    simp only [NNReal.coe_mul, NNReal.coe_natCast] at he
    have hSn : (∑ i ∈ Finset.range (n+1),
      ((h : ℝ)/2 * (∫ b, Y ((i : ℝ)*(h : ℝ)) b ∂W) +
      (∫ b, D ((i : ℝ)*(h : ℝ)) b (∫ t in ((i : ℝ)*(h : ℝ))..(((i+1 : ℕ) : ℝ)*(h : ℝ)), A t b) ∂W))) = S n := by
      simp only [S, h, NNReal.coe_div, NNReal.coe_natCast]
    rw [hSn] at he
    have hcoef : ((n+1 : ℕ) : ℝ) * C * (h : ℝ) = C*(T : ℝ) := by
      calc
        _ = C * (((n+1 : ℕ) : ℝ) * (h : ℝ)) := by ring
        _ = C*(T : ℝ) := by rw [hnr]
    rw [hcoef] at he
    simpa only [h, NNReal.coe_div, NNReal.coe_natCast] using he
  have he0 : Tendsto (fun n => |(∫ b, F T b ∂W) - (∫ b, F 0 b ∂W) - S n|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) herr (taylor_error_tendsto_zero T C K)
  have hed : Tendsto S atTop (𝓝 ((∫ b, F T b ∂W) - (∫ b, F 0 b ∂W))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have heq : (fun n => dist (S n) ((∫ b, F T b ∂W) - (∫ b, F 0 b ∂W))) =
        (fun n => |(∫ b, F T b ∂W) - (∫ b, F 0 b ∂W) - S n|) := by
      funext n
      rw [Real.dist_eq, abs_sub_comm]
    rw [heq]
    exact he0
  exact tendsto_nhds_unique hed hlim

end ExactSLEGenerator

namespace ExactSLEGenerator
variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma stronglyMeasurable_intervalIntegral_of_continuous [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (A : ℝ → Ω → E)
    (hc : ∀ b, Continuous (fun t => A t b)) (hm : ∀ t, Measurable (A t)) (u v : ℝ) :
    StronglyMeasurable (fun b => ∫ t in u..v, A t b) := by
  have hj : StronglyMeasurable (Function.uncurry A) :=
    (measurable_uncurry_of_continuous_of_measurable hc hm).stronglyMeasurable
  by_cases huv : u ≤ v
  · simp_rw [intervalIntegral.integral_of_le huv]
    exact hj.integral_prod_left
  · simp_rw [intervalIntegral.integral_of_ge (le_of_not_ge huv)]
    exact hj.integral_prod_left.neg

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

end ExactSLEGenerator
end

end OAI
