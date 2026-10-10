import Mathlib
import OAI.Probability.SKRatio.FiniteChain.DiscreteDistanceNonneg
import OAI.Probability.SKRatio.FiniteChain.Mean

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio
namespace Independent
variable {n : ℕ}

theorem distance_lower (hn : 2 ≤ n) (k : ℕ) {ε : ℝ}
    (hbound : 4 < ε * n * ((1 - 1 / (n : ℝ)) ^ k) ^ 2) :
    1 - ε < discreteDistance (0 : Disorder n) k := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have h := FiniteLaw.common_mass_square
    ((transition (0 : Disorder n) ^ k) (fun _ => true)) (mass 0 0) magnetization
    ((transition_pow_stochastic _ k).1 _) (mass_nonneg _ _)
    (Matrix.sum_row_of_mem_rowStochastic (transition_pow_stochastic _ k) _) (sum_mass _ _)
  rw [row_mean_magnetization hnpos, equilibrium_mean_magnetization, sub_zero,
    equilibrium_variance_magnetization] at h
  have hvar := row_variance_magnetization hn k
  have htv := tv_le_discreteDistance (0 : Disorder n) k (fun _ => true)
  by_contra hfail
  have hdist := le_of_not_gt hfail
  have hb := mul_lt_mul_of_pos_right hbound hnR
  have hpoint := mul_le_mul_of_nonneg_right
    (show ε ≤ 1 - totalVariation ((transition (0 : Disorder n) ^ k) (fun _ => true))
      (mass 0 0) from by linarith only [htv, hdist])
    (sq_nonneg ((n : ℝ) * (1 - 1 / (n : ℝ)) ^ k))
  nlinarith only [h, hvar, hb, hpoint]

def cutoffScale (n : ℕ) : ℝ := (n : ℝ) * Real.log n / 2

theorem cutoffScale_pos (hn : 2 ≤ n) : 0 < cutoffScale n := by
  have h : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)
  exact div_pos (mul_pos (by linarith) (Real.log_pos h)) (by norm_num)

theorem cutoffScale_tendsto : Tendsto cutoffScale atTop atTop := by
  have hl : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * Real.log n) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono' atTop _ hl
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  dsimp only [cutoffScale]
  nlinarith

theorem upper_exponent (hn : 2 ≤ n) (b : ℝ) :
    (n : ℝ) * Real.exp (-2 * (⌈(1 + b) * cutoffScale n⌉₊ : ℝ) / n) ≤
      Real.exp (-(b * Real.log n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hk := Nat.le_ceil ((1 + b) * cutoffScale n)
  have hexp : Real.log (n : ℝ) + -2 * (⌈(1 + b) * cutoffScale n⌉₊ : ℝ) / n ≤
      -(b * Real.log n) := by
    rw [show Real.log (n : ℝ) + -2 * (⌈(1 + b) * cutoffScale n⌉₊ : ℝ) / n =
      ((n : ℝ) * Real.log n - 2 * (⌈(1 + b) * cutoffScale n⌉₊ : ℝ)) / n from by field_simp; ring,
      div_le_iff₀ hnR]
    dsimp only [cutoffScale] at hk ⊢
    nlinarith only [hk]
  calc
    _ = Real.exp (Real.log (n : ℝ) + -2 * (⌈(1 + b) * cutoffScale n⌉₊ : ℝ) / n) := by
      rw [Real.exp_add, Real.exp_log hnR]
    _ ≤ _ := Real.exp_le_exp.mpr hexp

theorem one_spin_exp_lower (hn : 2 ≤ n) (k : ℕ) :
    Real.exp (-2 * (k : ℝ) / ((n : ℝ) - 1)) ≤ ((1 - 1 / (n : ℝ)) ^ k) ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hrpos : 0 < 1 - 1 / (n : ℝ) := by
    exact sub_pos.mpr ((div_lt_one hnpos).mpr (by linarith))
  have hlog : -1 / ((n : ℝ) - 1) ≤ Real.log (1 - 1 / (n : ℝ)) := by
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    convert Real.one_sub_inv_le_log_of_pos hrpos using 1
    field_simp [hn1]
    ring
  have hbase : Real.exp (-1 / ((n : ℝ) - 1)) ≤ 1 - 1 / (n : ℝ) := by
    calc
      _ ≤ Real.exp (Real.log (1 - 1 / (n : ℝ))) := Real.exp_le_exp.mpr hlog
      _ = _ := Real.exp_log hrpos
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _) hbase (2 * k)
  rw [← Real.exp_nat_mul] at hpow
  have hexp : (2 * k : ℕ) * (-1 / ((n : ℝ) - 1)) = -2 * (k : ℝ) / ((n : ℝ) - 1) := by
    push_cast
    ring
  simpa only [hexp, ← pow_mul, mul_comm k 2] using hpow

theorem lower_exponent (hn : 2 ≤ n) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hnb : 2 ≤ b * n) :
    Real.exp ((b / 2) * Real.log n) ≤
      (n : ℝ) * ((1 - 1 / (n : ℝ)) ^ ⌊(1 - b) * cutoffScale n⌋₊) ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hk := Nat.floor_le (show 0 ≤ (1 - b) * cutoffScale n from
    mul_nonneg (sub_pos.mpr hb1).le (cutoffScale_pos hn).le)
  have hmargin : (1 - b) * (n : ℝ) ≤ (1 - b / 2) * ((n : ℝ) - 1) := by
    nlinarith only [hnb, hb0]
  have hbound := mul_le_mul_of_nonneg_right hmargin hlog
  have hexp : (b / 2) * Real.log (n : ℝ) ≤
      Real.log n + -2 * (⌊(1 - b) * cutoffScale n⌋₊ : ℝ) / ((n : ℝ) - 1) := by
    rw [show Real.log (n : ℝ) + -2 * (⌊(1 - b) * cutoffScale n⌋₊ : ℝ) / ((n : ℝ) - 1) =
      (((n : ℝ) - 1) * Real.log n - 2 * (⌊(1 - b) * cutoffScale n⌋₊ : ℝ)) /
        ((n : ℝ) - 1) from by field_simp; ring,
      le_div_iff₀ hn1]
    dsimp only [cutoffScale] at hk ⊢
    nlinarith only [hk, hbound]
  calc
    _ ≤ Real.exp (Real.log (n : ℝ) +
        -2 * (⌊(1 - b) * cutoffScale n⌋₊ : ℝ) / ((n : ℝ) - 1)) :=
      Real.exp_le_exp.mpr hexp
    _ = (n : ℝ) * Real.exp (-2 * (⌊(1 - b) * cutoffScale n⌋₊ : ℝ) / ((n : ℝ) - 1)) := by
      rw [Real.exp_add, Real.exp_log hnpos]
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_spin_exp_lower hn _) hnpos.le

theorem distance_upper_eventually {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, discreteDistance (0 : Disorder n) ⌈(1 + b) * cutoffScale n⌉₊ ≤ ε := by
  have hlog : Tendsto (fun n : ℕ => b * Real.log n) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hb
  have hsmall : Tendsto (fun n : ℕ => Real.exp (Real.exp (-(b * Real.log n))) - 1)
      atTop (𝓝 0) := by
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlog
    simpa only [Real.exp_zero, sub_self, Function.comp_def] using
      (Real.continuous_exp.continuousAt.tendsto.comp hexp).sub_const 1
  have htarget : 0 < 4 * ε ^ 2 := by positivity
  filter_upwards [eventually_ge_atTop 2, hsmall.eventually (gt_mem_nhds htarget)] with n hn he
  apply distance_upper (lt_of_lt_of_le (by decide : 0 < 2) hn) _ hε.le
  exact (sub_le_sub_right (Real.exp_le_exp.mpr (upper_exponent hn b)) 1).trans he.le

theorem distance_lower_eventually {b ε : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 - ε < discreteDistance (0 : Disorder n) ⌊(1 - b) * cutoffScale n⌋₊ := by
  have hlog : Tendsto (fun n : ℕ => (b / 2) * Real.log n) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  have hlarge : Tendsto (fun n : ℕ => ε * Real.exp ((b / 2) * Real.log n)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp hlog).const_mul_atTop hε
  have hnb : Tendsto (fun n : ℕ => b * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hb0
  filter_upwards [eventually_ge_atTop 2, hnb.eventually_ge_atTop 2,
    hlarge.eventually_gt_atTop 4] with n hn hb he
  apply distance_lower hn
  exact he.trans_le (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (lower_exponent hn hb0 hb1 hb) hε.le)

theorem mixing_ratio_eventually {ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      (mixingTime (0 : Disorder n) ε : ℝ) / (mixingTime (0 : Disorder n) (1 - ε) : ℝ) ≤
        1 + η := by
  let b : ℝ := η / (2 * (2 + η))
  have hden : 0 < 2 * (2 + η) := by positivity
  have hb0 : 0 < b := div_pos hη hden
  have hb1 : b < 1 := (div_lt_one hden).mpr (by linarith)
  have hbid : b * (2 + η) = η / 2 := by
    dsimp only [b]
    field_simp
  have hbase : (1 + b) / (1 - b) < 1 + η := by
    apply (div_lt_iff₀ (sub_pos.mpr hb1)).mpr
    nlinarith only [hbid, hη]
  have hrem : Tendsto (fun n => 1 / ((1 - b) * cutoffScale n)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (cutoffScale_tendsto.const_mul_atTop (sub_pos.mpr hb1))
  have hevent := hrem.eventually (gt_mem_nhds (sub_pos.mpr hbase))
  filter_upwards [distance_lower_eventually hb0 hb1 hε0, distance_upper_eventually hb0 hε0,
    eventually_ge_atTop 2, hevent] with n hl hu hn hr
  have hratio := mixing_ratio_bound (0 : Disorder n) hε0 hε1 hb0 hb1 (cutoffScale_pos hn) hl hu
  linarith only [hr, hratio]

end Independent

theorem disorderLaw_zero_ae (n : ℕ) : ∀ᵐ g : Disorder n ∂disorderLaw 0 n, g = 0 := by
  have hs : disorderLaw 0 n ({0} : Set (Disorder n)) = 1 := by
    simp [disorderLaw, Measure.pi_singleton]
  rw [ae_iff]
  change disorderLaw 0 n ({0}ᶜ : Set (Disorder n)) = 0
  rw [measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), measure_univ, hs, tsub_self]

theorem ratio_cutoff_zero (ε η : ℝ) (hε0 : 0 < ε) (hεhalf : ε < 1 / 2) (hη : 0 < η) :
    Tendsto
      (fun n : ℕ => disorderLaw 0 n
        {g : Disorder n | 1 + η <
          (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1 - ε)) := by
  have hε1 : ε < 1 := by linarith
  refine ⟨?_, denominator_eventually_positive ε hε0 hε1⟩
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Independent.mixing_ratio_eventually hε0 hε1 hη] with n hn
  symm
  have hempty : ∀ᵐ g : Disorder n ∂disorderLaw 0 n,
      ¬ (1 + η < (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)) := by
    filter_upwards [disorderLaw_zero_ae n] with g hg
    subst g
    exact not_lt_of_ge hn
  simpa only [not_not] using ae_iff.mp hempty

end SKRatio

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

end
end
end
end

end OAI
