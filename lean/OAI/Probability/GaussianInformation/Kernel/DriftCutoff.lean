import Mathlib
import OAI.Probability.GaussianInformation.Kernel.ReferenceMarginals

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.DriftCutoff

noncomputable def level (d : ℕ) (H : ℝ) : ℕ := ⌈2*Real.log H+20*(d:ℝ)⌉₊+1

lemma level_pos (d : ℕ) (H : ℝ) : 0 < level d H := by unfold level; omega

lemma level_lower (d : ℕ) (H : ℝ) : 2*Real.log H+20*(d:ℝ) ≤ (level d H:ℝ) := by
  have h := Nat.le_ceil (2*Real.log H+20*(d:ℝ))
  unfold level
  push_cast
  linarith

lemma level_upper (d : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    (level d H:ℝ) ≤ 2*Real.log H+20*(d:ℝ)+2 := by
  have hh := Real.log_nonneg hH
  have h := Nat.ceil_lt_add_one (show 0 ≤ 2*Real.log H+20*(d:ℝ) by positivity)
  unfold level
  push_cast
  linarith

lemma log_constant_bound (d : ℕ) (hd : 16 ≤ d) {H : ℝ} (hH : 1 ≤ H) :
    Real.log (H*(9*3^d)*(4:ℝ)^(d-1)*(2:ℝ)^(2*(d/16)+1)) ≤
      (level d H:ℝ)*Real.log 2 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hlog2 : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hu2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hu3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<3 by norm_num)]
  have hu4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)]
  have hu9 : Real.log 9 ≤ 8 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<9 by norm_num)]
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_mul hHpos.ne' (by positivity),Real.log_mul (by norm_num) (by positivity)]
  simp only [Real.log_pow]
  have hdR : 16 ≤ (d:ℝ) := by exact_mod_cast hd
  have hn : ((d-1:ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.sub_le d 1
  have hk : ((2*(d/16)+1:ℕ):ℝ) ≤ (d:ℝ)+1 := by
    exact_mod_cast (show 2*(d/16)+1 ≤ d+1 by have hh := Nat.div_mul_le_self d 16; omega)
  have hL := level_lower d H
  have hp := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ) ≤ level d H by positivity)
  have h3 := mul_le_mul_of_nonneg_left hu3 (show (0:ℝ) ≤ d by positivity)
  have h4 := mul_le_mul_of_nonneg_left hu4 (show (0:ℝ) ≤ (d-1:ℕ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hu2 (show (0:ℝ) ≤ (2*(d/16)+1:ℕ) by positivity)
  linarith

lemma reference_cut (d : ℕ) (hd : 16 ≤ d) {H : ℝ} (hH : 1 ≤ H) :
    ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^(level d H)) ≤ 1 := by
  have hp := Real.le_pow_of_log_le (show (0:ℝ)<2 by norm_num) (log_constant_bound d hd hH)
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_one.mpr
  calc
    _ ≤ (2:ℝ)^(level d H)*(1/2:ℝ)^(level d H) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

lemma moment_cut (d : ℕ) (hd : 16 ≤ d) {H : ℝ} (hH : 1 ≤ H) :
    H*(9*3^d:ℝ) ≤ 2^(level d H) := by
  have hp := Real.le_pow_of_log_le (show (0:ℝ)<2 by norm_num) (log_constant_bound d hd hH)
  have h4 : (1:ℝ) ≤ 4^(d-1) := one_le_pow₀ (by norm_num)
  have h2 : (1:ℝ) ≤ 2^(2*(d/16)+1) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ H*(9*3^d:ℝ)*4^(d-1)*2^(2*(d/16)+1) := by
      have hpos : 0 ≤ H*(9*3^d:ℝ) := by positivity
      calc
        _ ≤ H*(9*3^d:ℝ)*4^(d-1) := le_mul_of_one_le_right hpos h4
        _ ≤ _ := le_mul_of_one_le_right (by positivity) h2
    _ ≤ _ := hp

lemma log_level_bound (d : ℕ) (hd : 1 ≤ d) {H : ℝ} (hH : 1 ≤ H) :
    Real.log ((level d H:ℝ)+2) ≤ 2*Real.log H/(d:ℝ)+25*(d:ℝ) := by
  have hdR : 1 ≤ (d:ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d:ℝ) := by linarith
  have hLpos : 0 < (level d H:ℝ)+2 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hLpos hdpos)
  rw [Real.log_div hLpos.ne' hdpos.ne'] at hlog
  have hlogd := Real.log_le_sub_one_of_pos hdpos
  have hLu := level_upper d hH
  have hbound : ((level d H:ℝ)+2)/(d:ℝ) ≤ 2*Real.log H/(d:ℝ)+24 := by
    apply (div_le_iff₀ hdpos).mpr
    have he : (2*Real.log H/(d:ℝ)+24)*(d:ℝ)=2*Real.log H+24*(d:ℝ) := by field_simp
    rw [he]
    linarith
  linarith

end KernelPotential.DriftCutoff

end OAI
