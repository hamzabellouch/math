import OAI.NumberTheory.TotientAsymptotic.TerminalStateMass

namespace OAI

/-! Absorption of the terminal allocation factor into Ford's logarithmic exponent. -/
noncomputable section
namespace TotientAsymptotic

lemma terminal_allocation_log_le {k : ℕ} (hk : 2 ≤ k) :
    Real.log ((k:ℝ)*(k+1)) ≤ 3*Real.log k := by
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hle : (k:ℝ)+1 ≤ (k:ℝ)^2 := by nlinarith
  have hh := Real.log_le_log (by linarith : (0:ℝ) < k+1) hle
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [Real.log_mul hk0.ne' (by linarith : (k:ℝ)+1 ≠ 0)]
  linarith

lemma terminal_allocation_log_budget {k : ℕ} {v : ℝ} (hk : 2 ≤ k)
    (hv : 1 < v) (hBv : 0 ≤ B v) :
    ((k:ℝ)*(k+1))^(4*(k:ℝ)*B v)*(Real.log v) ≤
      (Real.log v)^(20*(k:ℝ)*Real.log k+1) := by
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hbase : (0:ℝ) < (k:ℝ)*(k+1) := by positivity
  have hlogv : 0 < Real.log v := Real.log_pos hv
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have he : 4*(k:ℝ)*B v*Real.log ((k:ℝ)*(k+1)) ≤
      (20*(k:ℝ)*Real.log k)*B v := by
    have h := mul_le_mul_of_nonneg_left (terminal_allocation_log_le hk)
      (show 0 ≤ 4*(k:ℝ)*B v by positivity)
    nlinarith [mul_nonneg (mul_nonneg hk0.le hBv) hlogk]
  have hh : ((k:ℝ)*(k+1))^(4*(k:ℝ)*B v) ≤
      (Real.log v)^(20*(k:ℝ)*Real.log k) := by
    rw [Real.rpow_def_of_pos hbase,Real.rpow_def_of_pos hlogv]
    apply Real.exp_le_exp.mpr
    simpa only [B,mul_comm] using he
  calc
    _ ≤ (Real.log v)^(20*(k:ℝ)*Real.log k)*Real.log v :=
      mul_le_mul_of_nonneg_right hh hlogv.le
    _ = _ := by rw [Real.rpow_add hlogv,Real.rpow_one]

end TotientAsymptotic

end

end OAI
