import Mathlib
import OAI.NumberTheory.PiExponent.Analysis.AnalyticCollision
import OAI.NumberTheory.PiExponent.Approximation.RowTranslation

namespace OAI

open scoped BigOperators

namespace PiExponent.LogTailAnalytic

noncomputable def logTail (T : ℕ) (z : ℂ) : ℂ :=
  Complex.logTaylor T z - Complex.log (1 + z)

theorem eval_trunc_log (T : ℕ) (z : ℂ) :
    (PowerSeries.trunc T (PowerSeries.log ℂ)).eval z = Complex.logTaylor T z := by
  change (PowerSeries.trunc T (PowerSeries.log ℂ)).eval₂ (RingHom.id ℂ) z = _
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  unfold Complex.logTaylor
  apply Finset.sum_congr rfl
  intro n hn
  simp only [RingHom.id_apply, PowerSeries.coeff_log]
  by_cases h : n = 0
  · simp [h]
  · simp [h, map_div₀, map_pow]
    ring

theorem analyticAt_logTail (T : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (logTail T) z := by
  unfold logTail Complex.logTaylor
  apply AnalyticAt.sub
  · apply Finset.analyticAt_fun_sum
    intro n hn
    fun_prop
  · exact (analyticAt_const.add analyticAt_id).clog (Complex.mem_slitPlane_of_norm_lt_one hz)

 theorem norm_logTail_le (T : ℕ) (hT : 1 ≤ T) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖logTail T z‖ ≤ ‖z‖ ^ T * (1 - ‖z‖)⁻¹ / T := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  unfold logTail
  rw [norm_sub_rev]
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    Complex.norm_log_sub_logTaylor_le n hz

theorem norm_logTail_le_one (T : ℕ) (hT : 1 ≤ T) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖logTail T z‖ ≤ 1 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hpow : ‖z‖ ^ T ≤ 1 / 2 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
    rw [pow_succ]
    have hh : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg z) hz1.le
    nlinarith [norm_nonneg z]
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : 0 < 1 - ‖z‖) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  calc
    ‖logTail T z‖ ≤ ‖z‖ ^ T * (1 - ‖z‖)⁻¹ / T := norm_logTail_le T hT hz1
    _ ≤ (1 / 2 : ℝ) * 2 / T := by gcongr
    _ ≤ 1 := by rw [div_le_iff₀ (by positivity : (0 : ℝ) < T)]; nlinarith

theorem norm_prod_logTail_le_one {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (hT : ∀ i ∈ s, 1 ≤ T i) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖∏ i ∈ s, logTail (T i) z ^ d i‖ ≤ 1 := by
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro i hi
    positivity
  · intro i hi
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_logTail_le_one (T i) (hT i hi) hz)

theorem analyticAt_prod_logTail {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (fun t => ∏ i ∈ s, logTail (T i) t ^ d i) z := by
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact (analyticAt_logTail (T i) hz).pow (d i)

theorem norm_rowTest_prod_logTail_le {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (hT : ∀ i ∈ s, 1 ≤ T i) (k : ℕ) :
    ‖AnalyticCollision.rowTest k (fun z => ∏ i ∈ s, logTail (T i) z ^ d i)‖ ≤
      (2 : ℝ) ^ k := by
  have h := AnalyticCollision.norm_rowTest_le
    (f := fun z => ∏ i ∈ s, logTail (T i) z ^ d i) (D := 1) ?_ k
  · simpa only [mul_one] using h
  intro z hz
  apply norm_prod_logTail_le_one s T d hT
  exact (by simpa only [Metric.mem_sphere, dist_zero_right] using hz : ‖z‖ = 1 / 2).le

theorem logTail_isBigO (T : ℕ) (hT : 1 ≤ T) :
    (fun z => logTail T z) =O[nhds (0 : ℂ)] (fun z => z ^ T) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  have h := (Complex.log_sub_logTaylor_isBigO n).neg_left
  simpa only [logTail, neg_sub, Nat.succ_eq_add_one] using h

theorem order_formal_logTail (T : ℕ) :
    (T : ℕ∞) ≤ (RowTranslation.tail T (PowerSeries.log ℂ)).order :=
  RowTranslation.order_tail T (PowerSeries.log ℂ)

theorem hasSum_formal_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.log ℂ) * z ^ n)
      (Complex.log (1 + z)) := by
  convert Complex.hasSum_taylorSeries_log hz using 1
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · simp [PowerSeries.coeff_log, hn, map_div₀, map_pow]
    ring

theorem hasSum_trunc_log (T : ℕ) (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n
      (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) * z ^ n)
      (Complex.logTaylor T z) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := Finset.range T)
    (f := fun n => PowerSeries.coeff n
      (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) * z ^ n) ?_
  · convert h using 1
    rw [← eval_trunc_log]
    change (PowerSeries.trunc T (PowerSeries.log ℂ)).eval₂ (RingHom.id ℂ) z = _
    rw [PowerSeries.eval₂_trunc_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    simp [PowerSeries.coeff_trunc, Finset.mem_range.mp hn]
  · intro n hn
    have hn' : ¬ n < T := by simpa only [Finset.mem_range] using hn
    simp [PowerSeries.coeff_trunc, hn']

theorem hasSum_formal_logTail (T : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n
      (RowTranslation.tail T (PowerSeries.log ℂ)) * z ^ n) (logTail T z) := by
  convert (hasSum_trunc_log T z).sub (hasSum_formal_log hz) using 1
  · funext n
    simp only [RowTranslation.tail, map_sub, sub_mul]
  · rfl

theorem hasFPowerSeriesAt_logTail (T : ℕ) :
    HasFPowerSeriesAt (logTail T)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff n (RowTranslation.tail T (PowerSeries.log ℂ)))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using
    hasSum_formal_logTail T hn

theorem hasSum_coeff_mul {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f * g) * z ^ n) (x * y) := by
  have hfn := hf.summable.norm
  have hgn := hg.summable.norm
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at heq
  rw [← heq] at hs
  convert hs using 1
  funext n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have he : a.1 + a.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
  rw [← he, pow_add]
  ring

theorem hasSum_coeff_one (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) 1 := by
  convert hasSum_ite_eq 0 (1 : ℂ) using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

 theorem hasSum_coeff_pow {f : PowerSeries ℂ} {x z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x) (d : ℕ) :
    HasSum (fun n => PowerSeries.coeff n (f ^ d) * z ^ n) (x ^ d) := by
  induction d with
  | zero => simpa only [pow_zero] using hasSum_coeff_one z
  | succ d hd => simpa only [pow_succ] using hasSum_coeff_mul hd hf

theorem hasSum_formal_prod_logTail {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n
      (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i) * z ^ n)
      (∏ i ∈ s, logTail (T i) z ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using hasSum_coeff_one z
  | @insert i s hi hs =>
    simpa only [Finset.prod_insert hi] using
      hasSum_coeff_mul (hasSum_coeff_pow (hasSum_formal_logTail (T i) hz) (d i)) hs

theorem hasFPowerSeriesAt_prod_logTail {ι : Type*} (s : Finset ι) (T d : ι → ℕ) :
    HasFPowerSeriesAt (fun z => ∏ i ∈ s, logTail (T i) z ^ d i)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff n
          (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using
    hasSum_formal_prod_logTail s T d hn

theorem rowTest_prod_logTail_eq_coeff {ι : Type*} (s : Finset ι) (T d : ι → ℕ) (k : ℕ) :
    AnalyticCollision.rowTest k (fun z => ∏ i ∈ s, logTail (T i) z ^ d i) =
      PowerSeries.coeff k (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i) := by
  have hd : DifferentiableOn ℂ (fun z => ∏ i ∈ s, logTail (T i) z ^ d i)
      (Metric.closedBall 0 (1 / 2)) := by
    intro z hz
    apply (analyticAt_prod_logTail s T d ?_).differentiableAt.differentiableWithinAt
    have hz' : ‖z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    linarith
  have hp := hd.hasFPowerSeriesOnBall (R := (1 / 2 : NNReal)) (by norm_num)
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesAt_prod_logTail s T d)
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p k (fun _ => 1)) he
  simpa only [AnalyticCollision.rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh

theorem norm_coeff_prod_formal_logTail_le {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (hT : ∀ i ∈ s, 1 ≤ T i) (k : ℕ) :
    ‖PowerSeries.coeff k (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i)‖ ≤
      (2 : ℝ) ^ k := by
  rw [← rowTest_prod_logTail_eq_coeff]
  exact norm_rowTest_prod_logTail_le s T d hT k

theorem rowTest_tail_budget {ι : Type*} (s : Finset ι) (T d : ι → ℕ) (k : ℕ)
    (hk : AnalyticCollision.rowTest k (fun z => ∏ i ∈ s, logTail (T i) z ^ d i) ≠ 0) :
    ∑ i ∈ s, d i * T i ≤ k := by
  rw [rowTest_prod_logTail_eq_coeff] at hk
  exact RowTranslation.tail_budget_nat s T d (fun _ => PowerSeries.log ℂ) k hk

end PiExponent.LogTailAnalytic

end OAI
