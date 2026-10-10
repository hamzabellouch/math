import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem prefix_failure_envelope_superpolynomial (K : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)^K *
      Real.exp (- (Real.log n)^(4/3 : ℝ))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (Real.log (n : ℝ))^(1/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp hlog
  have hbound : ∀ᶠ n : ℕ in atTop, (n : ℝ)^K *
      Real.exp (- (Real.log n)^(4/3 : ℝ)) ≤ (n : ℝ)^(-1 : ℝ) := by
    filter_upwards [hpow.eventually (eventually_ge_atTop (K+1)),
      eventually_ge_atTop (2 : ℕ)] with n hn hsize
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn1
    have hl0 : 0 < Real.log (n : ℝ) := Real.log_pos hn1
    have he : (Real.log (n : ℝ))^(4/3 : ℝ) =
        Real.log n * (Real.log n)^(1/3 : ℝ) := by
      rw [show (4/3 : ℝ) = 1+1/3 by norm_num,Real.rpow_add hl0,Real.rpow_one]
    have hle : (K+1)*Real.log n ≤ (Real.log (n : ℝ))^(4/3 : ℝ) := by
      rw [he,mul_comm (K+1)]
      exact mul_le_mul_of_nonneg_left hn hl0.le
    calc
      (n : ℝ)^K * Real.exp (- (Real.log n)^(4/3 : ℝ)) ≤
          (n : ℝ)^K * (n : ℝ)^(-(K+1)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
        rw [Real.rpow_def_of_pos hn0]
        apply Real.exp_le_exp.mpr
        nlinarith only [hle]
      _ = (n : ℝ)^(-1 : ℝ) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
  exact squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) hbound
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
      tendsto_natCast_atTop_atTop)

theorem prefix_failure_l2_envelope_tendsto :
    Tendsto (fun n : ℕ => (2*(n : ℝ)+1)*
      Real.exp (- (Real.log n)^(4/3 : ℝ))) atTop (𝓝 0) := by
  have h1 := prefix_failure_envelope_superpolynomial 1
  have h0 := prefix_failure_envelope_superpolynomial 0
  simpa only [Real.rpow_one,Real.rpow_zero,one_mul,mul_add,add_mul,mul_zero,
    add_zero,Function.comp_def,mul_assoc] using (h1.const_mul 2).add h0

end SharpTerminalLeave

end

end OAI
