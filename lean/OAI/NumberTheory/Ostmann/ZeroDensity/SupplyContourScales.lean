import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Estimates.NonquadraticZeroFree
import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyPrimeScales

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.ZeroDensity

def supplyContourHeight (P : ℕ) (E L : ℝ) : ℕ :=
  2*(supplyConductorCutoff L)^P*⌈Real.exp (E*L)⌉₊

theorem supplyContourHeight_ge_two (P : ℕ) (E L : ℝ) :
    2 ≤ supplyContourHeight P E L := by
  have hQ := supplyConductorCutoff_pos L
  have he := Nat.ceil_pos.mpr (Real.exp_pos (E*L))
  have hp : 0 < (supplyConductorCutoff L)^P*⌈Real.exp (E*L)⌉₊ := by positivity
  unfold supplyContourHeight
  nlinarith

theorem supplyContourHeight_lower (P : ℕ) (E L : ℝ) :
    2*(supplyConductorCutoff L : ℝ)^P*Real.exp (E*L) ≤ supplyContourHeight P E L := by
  unfold supplyContourHeight
  push_cast
  exact mul_le_mul_of_nonneg_left (Nat.le_ceil (Real.exp (E*L))) (by positivity)

theorem supplyContourHeight_log_le (P : ℕ) {E L : ℝ} (hE : 0 ≤ E) (hL : 1 ≤ L) :
    Real.log (supplyContourHeight P E L : ℝ) ≤
      P*Real.log (supplyConductorCutoff L : ℝ)+(E+2)*L := by
  have hQ : (0 : ℝ) < supplyConductorCutoff L :=
    Nat.cast_pos.mpr (supplyConductorCutoff_pos L)
  have hCeil : (0 : ℝ) < (⌈Real.exp (E*L)⌉₊ : ℕ) := by
    exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos (E*L))
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos (E*L)).le
  have he : 1 ≤ Real.exp (E*L) := Real.one_le_exp (by positivity)
  have hupper : (⌈Real.exp (E*L)⌉₊ : ℝ) ≤ 2*Real.exp (E*L) := by linarith
  have hlogceil := Real.log_le_log hCeil hupper
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hlogceil
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  unfold supplyContourHeight
  push_cast
  rw [Real.log_mul (by positivity) hCeil.ne',
    Real.log_mul (by norm_num) (pow_pos hQ P).ne', Real.log_pow]
  linarith

theorem supplyContourHeight_modulus_budget (P : ℕ) {E L : ℝ}
    (hE : 0 ≤ E) (hL : 1 ≤ L) :
    Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight (supplyConductorCutoff L)
      (supplyContourHeight P E L : ℝ) ≤
        (20003*((P : ℝ)+1)+E+8)*L*Real.exp (9*L/10) := by
  have hH : (2 : ℝ) ≤ supplyContourHeight P E L := by
    exact_mod_cast supplyContourHeight_ge_two P E L
  have hHp : (0 : ℝ) < supplyContourHeight P E L := by linarith
  have hlog := Real.log_le_log (show (0 : ℝ) < supplyContourHeight P E L+6 by positivity)
    (show (supplyContourHeight P E L : ℝ)+6 ≤ 7*supplyContourHeight P E L by linarith)
  rw [Real.log_mul (by norm_num) hHp.ne'] at hlog
  have hlog7 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<7)
  have hHL := supplyContourHeight_log_le P hE hL
  have hQL := log_supplyConductorCutoff_bound hL
  have he : 1 ≤ Real.exp (9*L/10) := Real.one_le_exp (by positivity)
  unfold Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight
  rw [abs_of_pos hHp]
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hmul := mul_le_mul_of_nonneg_left hQL (show 0 ≤ (P : ℝ)+1 by positivity)
  have hExtra : (E+8)*L ≤ (E+8)*L*Real.exp (9*L/10) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he
      (show 0 ≤ (E+8)*L by positivity)
  nlinarith

theorem modulusHeight_nat_succ_le (Q H : ℕ) :
    Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q ((H+1 : ℕ) : ℝ) ≤
      Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ)+1 := by
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hl := Real.log_le_log (show (0 : ℝ)<(H : ℝ)+7 by positivity)
    (show (H : ℝ)+7 ≤ 2*((H : ℝ)+6) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hl
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  unfold Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight
  rw [abs_of_nonneg (Nat.cast_nonneg (H+1)), abs_of_nonneg hH]
  push_cast
  have he : (H : ℝ)+1+6 = H+7 := by ring
  rw [he]
  linarith

theorem supplyContourHeight_succ_modulus_budget (P : ℕ) {E L : ℝ}
    (hE : 0 ≤ E) (hL : 1 ≤ L) :
    Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight (supplyConductorCutoff L)
      ((supplyContourHeight P E L+1 : ℕ) : ℝ) ≤
        (20003*((P : ℝ)+1)+E+9)*L*Real.exp (9*L/10) := by
  have h1 := modulusHeight_nat_succ_le (supplyConductorCutoff L) (supplyContourHeight P E L)
  have h2 := supplyContourHeight_modulus_budget P hE hL
  have he : 1 ≤ Real.exp (9*L/10) := Real.one_le_exp (by positivity)
  nlinarith

end Ostmann.ZeroDensity

end

end OAI
