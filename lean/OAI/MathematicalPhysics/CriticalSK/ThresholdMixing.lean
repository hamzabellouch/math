import OAI.MathematicalPhysics.CriticalSK.VariationalDefinitions
import OAI.MathematicalPhysics.CriticalSK.ThresholdContraction

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
namespace CriticalSK

section SKThresholdComparison
variable {n : ℕ} (W : Disorder n)

lemma continuousKernel_nat_mul (t : ℝ) (k : ℕ) :
    continuousKernel W ((k : ℝ) * t) = continuousKernel W t ^ k := by
  induction k with
  | zero => simp [continuousKernel]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, continuousKernel_add, ih,
      pow_succ]

lemma continuousDistance_iteration (hn : 0 < n) {t ε : ℝ} (ht : 0 ≤ t)
    (hε : 0 ≤ ε) (hb : ∀ x, continuousDistance W t x ≤ ε) (k : ℕ) (x : Spin n) :
    continuousDistance W ((k : ℝ) * t) x ≤ (2 * ε) ^ k := by
  have hh := kernel_power_tv_bound (continuousKernel_nonneg W hn t ht)
    (gibbs_nonneg W) (continuousKernel_sum W hn t) (gibbs_sum W)
    (continuousKernel_stationary W hn t) (mul_nonneg (by norm_num) hε)
    (show ∀ x, (1 / 2 : ℝ) * ∑ y, |continuousKernel W t x y - gibbs W y| ≤
        (2 * ε) / 2 by simpa only [continuousDistance, totalVariation,
          mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hb)
    k x
  simpa only [continuousDistance, totalVariation, continuousKernel_nat_mul] using hh

lemma discreteDistance_iteration (hn : 0 < n) {l : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (hb : ∀ x, discreteDistance W l x ≤ ε) (k : ℕ) (x : Spin n) :
    discreteDistance W (l * k) x ≤ (2 * ε) ^ k := by
  have hh := kernel_power_tv_bound (kernel_pow_nonneg (discreteKernel_nonneg W) l)
    (gibbs_nonneg W) (kernel_pow_sum (discreteKernel_sum W hn) l) (gibbs_sum W)
    (kernel_pow_stationary (discreteKernel_stationary W hn) l)
    (mul_nonneg (by norm_num) hε)
    (show ∀ x, (1 / 2 : ℝ) * ∑ y, |(discreteKernel W ^ l) x y - gibbs W y| ≤
        (2 * ε) / 2 by simpa only [discreteDistance, totalVariation,
          mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hb)
    k x
  simpa only [discreteDistance, totalVariation, pow_mul] using hh

lemma continuousMixingAt_set_nonempty (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    {t : ℝ | 0 ≤ t ∧ ∀ x, continuousDistance W t x ≤ ε}.Nonempty := by
  obtain ⟨t, ht, hb⟩ := continuous_mixing_set_nonempty W hn
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 * (1 / 4) : ℝ) < 1)
  refine ⟨(m : ℝ) * t, mul_nonneg (Nat.cast_nonneg _) ht, fun x => ?_⟩
  exact (continuousDistance_iteration W hn ht (by norm_num) hb m x).trans hm.le

lemma discreteMixingAt_set_nonempty (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    {k : ℕ | ∀ x, discreteDistance W k x ≤ ε}.Nonempty := by
  obtain ⟨l, hb⟩ := discrete_mixing_set_nonempty W hn
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 * (1 / 4) : ℝ) < 1)
  exact ⟨l * m, fun x => (discreteDistance_iteration W hn (by norm_num) hb m x).trans hm.le⟩

lemma continuousMixingAt_quarter_comparison (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 0 < m) (hpow : (2 * ε) ^ m ≤ 1 / 4) :
    continuousMixingTime W ≤ (m : ℝ) * continuousMixingAt W ε := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  suffices h : continuousMixingTime W / (m : ℝ) ≤ continuousMixingAt W ε by
    simpa only [mul_comm] using (div_le_iff₀ hmR).mp h
  apply le_csInf (continuousMixingAt_set_nonempty W hn hε)
  intro t ht
  apply (div_le_iff₀ hmR).mpr
  have hb : ∀ x, continuousDistance W ((m : ℝ) * t) x ≤ 1 / 4 := fun x =>
    (continuousDistance_iteration W hn ht.1 hε.le ht.2 m x).trans hpow
  simpa only [mul_comm] using continuousMixingTime_le_of_distance W
    (mul_nonneg hmR.le ht.1) hb

lemma discreteMixingAt_quarter_comparison (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hpow : (2 * ε) ^ m ≤ 1 / 4) :
    discreteMixingTime W ≤ m * discreteMixingAt W ε := by
  have hb : ∀ x, discreteDistance W (discreteMixingAt W ε) x ≤ ε :=
    Nat.sInf_mem (discreteMixingAt_set_nonempty W hn hε)
  have hqm : ∀ x, discreteDistance W (discreteMixingAt W ε * m) x ≤ 1 / 4 := fun x =>
    (discreteDistance_iteration W hn hε.le hb m x).trans hpow
  simpa only [mul_comm] using discreteMixingTime_le_of_distance W hqm

end SKThresholdComparison

lemma exists_threshold_amplification {ε : ℝ} (hεhalf : ε < 1 / 2) :
    ∃ m : ℕ, 0 < m ∧ (2 * ε) ^ m ≤ 1 / 4 := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 4)
    (by linarith : 2 * ε < 1)
  refine ⟨m, ?_, hm.le⟩
  by_contra h
  have he : m = 0 := by omega
  norm_num [he] at hm

theorem critical_mixing_lower_bounds_at (ε : ℝ) (hε : 0 < ε)
    (hεhalf : ε < 1 / 2) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (disorderLaw n).real
      {W | (n : ℝ) ^ (2 / 3 - δ) ≤ continuousMixingAt W ε}) atTop (𝓝 1) ∧
    Tendsto (fun n => (disorderLaw n).real
      {W | (n : ℝ) ^ (5 / 3 - δ) ≤ (discreteMixingAt W ε : ℝ)}) atTop (𝓝 1) := by
  obtain ⟨m, hm, hpow⟩ := exists_threshold_amplification hεhalf
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  constructor
  · have hscale : Tendsto (fun n : ℕ => ((m : ℝ) * (n : ℝ) ^ (2 / 3 - δ)) /
        (n : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_div_assoc, mul_zero] using
        (rpow_ratio_tendsto_zero (a := 2 / 3) hδ).const_mul (m : ℝ)
    have hp := continuousMixingTime_lower_limit
      (fun n => (m : ℝ) * (n : ℝ) ^ (2 / 3 - δ)) (fun _ => by positivity) hscale
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [(tendsto_order.mp hp).1 a ha, eventually_gt_atTop 0] with n hn hnpos
      refine lt_of_lt_of_le hn (measureReal_mono ?_)
      intro W hW
      have hc := continuousMixingAt_quarter_comparison W hnpos hε hm hpow
      exact (mul_le_mul_iff_right₀ hmR).mp (show (m : ℝ) * (n : ℝ) ^ (2 / 3 - δ) ≤
        (m : ℝ) * continuousMixingAt W ε from hW.trans hc)
    · intro a ha
      exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt measureReal_le_one ha)
  · have hscale : Tendsto (fun n : ℕ =>
        ((m * ⌈(n : ℝ) ^ (5 / 3 - δ)⌉₊ : ℕ) : ℝ) / (n : ℝ) ^ (5 / 3 : ℝ))
        atTop (𝓝 0) := by
      simpa only [Nat.cast_mul, mul_div_assoc, mul_zero] using
        (ceil_rpow_ratio_tendsto_zero (a := 5 / 3) (by norm_num) hδ).const_mul (m : ℝ)
    have hp := discreteMixingTime_lower_limit (fun n => m * ⌈(n : ℝ) ^ (5 / 3 - δ)⌉₊) hscale
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [(tendsto_order.mp hp).1 a ha, eventually_gt_atTop 0] with n hn hnpos
      refine lt_of_lt_of_le hn (measureReal_mono ?_)
      intro W hW
      have hc := discreteMixingAt_quarter_comparison W hnpos hε hpow
      have hh : m * ⌈(n : ℝ) ^ (5 / 3 - δ)⌉₊ ≤ m * discreteMixingAt W ε := hW.trans hc
      have hcast : (m : ℝ) * (⌈(n : ℝ) ^ (5 / 3 - δ)⌉₊ : ℝ) ≤
          (m : ℝ) * (discreteMixingAt W ε : ℝ) := by exact_mod_cast hh
      exact (Nat.le_ceil _).trans ((mul_le_mul_iff_right₀ hmR).mp hcast)
    · intro a ha
      exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt measureReal_le_one ha)

end CriticalSK
end

end OAI
