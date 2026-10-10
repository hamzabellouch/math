import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.WitnessMu

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma endpoint_marks_exponential (s : ℕ) :
    ((s : ℝ)+4)^2 ≤ 32*(5/4 : ℝ)^s := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    by_cases hs : s < 5
    · interval_cases s <;> norm_num
    · have hn : (5 : ℝ) ≤ s := by exact_mod_cast Nat.le_of_not_gt hs
      have hstep : ((s : ℝ)+5)^2 ≤ (5/4 : ℝ)*((s : ℝ)+4)^2 := by
        nlinarith [sq_nonneg ((s : ℝ)-5)]
      have hh := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 5/4)
      simp only [Nat.cast_add,Nat.cast_one,pow_succ]
      nlinarith

lemma pattern_marks_exponential {R s : ℕ} (hR : R ≤ 4) :
    (((R+s)^2 * 6^s : ℕ) : ℝ) ≤ 32*(15/2 : ℝ)^s := by
  have hr : (R : ℝ) ≤ 4 := by exact_mod_cast hR
  have hp : ((R : ℝ)+(s : ℝ))^2 ≤ ((s : ℝ)+4)^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith : (R : ℝ)+(s : ℝ) ≤ (s : ℝ)+4) 2
  push_cast
  calc
    _ ≤ (((s : ℝ)+4)^2)*(6 : ℝ)^s :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ (32*(5/4 : ℝ)^s)*(6 : ℝ)^s :=
      mul_le_mul_of_nonneg_right (endpoint_marks_exponential s) (by positivity)
    _ = 32*(15/2 : ℝ)^s := by rw [mul_assoc,← mul_pow]; norm_num

theorem generous_witness_length_sum {D : ℝ} (hD : 0 < D) :
    (1 + 2*D)^3 * (∑' h : ℕ, ∑' a : ℕ, ∑' b : ℕ,
      (30*D*witnessMu D)^(h+a+b) /
        ((h.factorial : ℝ)*(a.factorial : ℝ)*(b.factorial : ℝ))) =
      (1+2*D)^48 := by
  rw [three_segment_series]
  have he : 3*(30*D*witnessMu D) = 45*Real.log (1+2*D) := by
    unfold witnessMu
    field_simp
    ring
  rw [he,show (45 : ℝ) = (45 : ℕ) by norm_num,Real.exp_nat_mul,
    Real.exp_log (by linarith : 0 < 1+2*D)]
  rw [← pow_add]

theorem generous_witness_power_bound {D : ℝ} (hD : 1 ≤ D) :
    32*(1+2*D)^48 / D^50 ≤ 32*(3 : ℝ)^48 / D^2 := by
  have hpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hm : (1+2*D)^48 ≤ (3*D)^48 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 32))
    (le_of_lt (pow_pos hpos 50))
  apply hh.trans_eq
  rw [mul_pow,show 50=48+2 by norm_num,pow_add]
  field_simp

theorem generous_witness_scaled_tendsto :
    Tendsto (fun D : ℝ => D*(32*(1+2*D)^48/D^50)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun D : ℝ => 32*(3 : ℝ)^48 / D) atTop (𝓝 0) := by
    have ht := (tendsto_inv_atTop_zero : Tendsto (fun D : ℝ => D⁻¹) atTop (𝓝 0)).const_mul
      (32*(3 : ℝ)^48)
    simpa only [mul_zero,div_eq_mul_inv] using ht
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
    have hpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    have hh := mul_le_mul_of_nonneg_left (generous_witness_power_bound hD) hpos.le
    apply hh.trans_eq
    field_simp

end SharpTerminalLeave

end

end OAI
