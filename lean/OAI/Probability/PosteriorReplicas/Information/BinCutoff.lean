import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

def binCutoff (d k : ℕ) (L : ℝ) : ℕ := 7*d+k+2+Nat.ceil (2*Real.log L)

lemma real_pow_cutoff {d k : ℕ} {L : ℝ} (hL : 1 ≤ L) :
    L*(72:ℝ)^d*(1/2)^binCutoff d k L*(1+2^(k+1)) ≤ 1 := by
  have hLp : 0 < L := by linarith
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hceil := Nat.le_ceil (2*Real.log L)
  have hpowL : L ≤ (2:ℝ)^Nat.ceil (2*Real.log L) := by
    apply (Real.log_le_log_iff hLp (by positivity)).mp
    rw [Real.log_pow]
    nlinarith [mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α:=ℝ) (Nat.ceil (2*Real.log L)))]
  have h72 : (72:ℝ)^d ≤ 2^(7*d) := by
    calc
      _ ≤ ((2:ℝ)^7)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
      _ = _ := (pow_mul _ _ _).symm
  have hsum : (1:ℝ)+2^(k+1) ≤ 2^(k+2) := by
    have h := one_le_pow₀ (show (1:ℝ)≤2 by norm_num) (n:=k+1)
    norm_num [pow_add] at h ⊢
    linarith
  have hp : L*(72:ℝ)^d*(1+2^(k+1)) ≤ 2^binCutoff d k L := by
    calc
      _ ≤ (2:ℝ)^Nat.ceil (2*Real.log L)*2^(7*d)*2^(k+2) :=
        mul_le_mul (mul_le_mul hpowL h72 (by positivity) (by positivity)) hsum (by positivity) (by positivity)
      _ = _ := by rw [← pow_add,← pow_add]; congr 1; unfold binCutoff; omega
  calc
    _ = (L*(72:ℝ)^d*(1+2^(k+1)))*(1/2)^binCutoff d k L := by ring
    _ ≤ (2:ℝ)^binCutoff d k L * (1/2)^binCutoff d k L := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

lemma binCutoff_bound {d k : ℕ} (hk : k≤d) {L : ℝ} (hL : 1≤L) :
    (binCutoff d k L : ℝ)+2 ≤ 16*(1+(d:ℝ)+Real.log L) := by
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.log_nonneg hL))).le
  have hkr : (k:ℝ)≤d := by exact_mod_cast hk
  unfold binCutoff
  push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) d,Real.log_nonneg hL]

lemma binCutoff_valid {d k : ℕ} {L : ℝ} (hL : 1≤L) :
    (ENNReal.ofReal L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^binCutoff d k L)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1 := by
  have hh := ENNReal.ofReal_le_ofReal (real_pow_cutoff (d:=d) (k:=k) hL)
  have hL0 : 0 ≤ L := by linarith
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul hL0,
    ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2)] at hh
  simpa only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using hh

lemma binCutoff_log_bound {d k : ℕ} (hk : k≤d) {L : ℝ} (hL : 1≤L) :
    Real.log ((binCutoff d k L:ℝ)+2) ≤ 16+Real.log (1+(d:ℝ)+Real.log L) := by
  have ha : 0 < 1+(d:ℝ)+Real.log L := by linarith [Nat.cast_nonneg (α:=ℝ) d,Real.log_nonneg hL]
  have hh := Real.log_le_log (by positivity : 0<(binCutoff d k L:ℝ)+2) (binCutoff_bound hk hL)
  rw [Real.log_mul (by norm_num) ha.ne'] at hh
  linarith [Real.log_le_self (by norm_num : (0:ℝ)≤16)]

end PosteriorReplicas
end

end OAI
