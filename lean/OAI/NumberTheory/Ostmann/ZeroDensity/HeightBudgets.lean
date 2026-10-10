import OAI.NumberTheory.Ostmann.ZeroDensity.Scales
import OAI.NumberTheory.Ostmann.ZeroDensity.ZeroFreeWeights

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.ZeroDensity

theorem conductor_height_log_le (Q H : ℕ) (hQ : 0 < Q) (hH : 0 < H) :
    Real.log (Q*H : ℕ) ≤ Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ) := by
  have hqp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hhp : (0 : ℝ) < H := by exact_mod_cast hH
  have hh := Real.log_le_log hhp (show (H : ℝ) ≤ H+6 by linarith)
  unfold Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight
  rw [abs_of_nonneg hhp.le, Nat.cast_mul, Real.log_mul hqp.ne' hhp.ne']
  linarith

theorem density_height_log_le (Q H : ℕ) (hQ : 0 < Q) (hH : 0 < H) :
    Real.log (Q^2*H : ℕ) ≤ 2*Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ) := by
  have hqp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hhp : (0 : ℝ) < H := by exact_mod_cast hH
  have hhn : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  have hh := Real.log_le_log hhp (show (H : ℝ) ≤ H+6 by linarith)
  unfold Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight
  rw [abs_of_nonneg hhp.le, Nat.cast_mul, Nat.cast_pow,
    Real.log_mul (by positivity) hhp.ne', Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem density_height_gap_gain {c B L M Y : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hL : 0 < L) (hY : 0 < Y) (hM : Real.exp L ≤ M)
    (hYB : Y ≤ B*L*Real.exp (9*L/10)) :
    (c/(2*B))*Real.exp (L/10)/L ≤ M*(c/Y)/2 := by
  have he : Real.exp L = Real.exp (L/10)*Real.exp (9*L/10) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (c/(2*B))*Real.exp (L/10)/L =
        Real.exp L*(c/(B*L*Real.exp (9*L/10)))/2 := by
      rw [he]
      field_simp
    _ ≤ M*(c/Y)/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul hM (div_le_div_of_nonneg_left hc.le hY hYB)
        (by positivity) (lt_of_lt_of_le (Real.exp_pos L) hM).le

end Ostmann.ZeroDensity

end

end OAI
