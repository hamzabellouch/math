import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySparseLargeValues

theorem sparse_card_of_moment {a H N B V : ℝ} {r k : ℕ}
    (ha : 0 ≤ a) (hH : 1 ≤ H) (hN : 2 ≤ N) (hB : 1 ≤ B) (hV : 0 < V)
    (hr : 0 < r) (hk : 4*r ≤ k)
    (hmoment : a ≤ H*(B/N)^k/V^(2*k))
    (hupper : H ≤ (2*N)^(k+1))
    (hsize : (2*B)^(8*r) ≤ N) (hthreshold : 1 ≤ N*V^(8*r)) :
    a^r ≤ H := by
  by_cases ha0 : a = 0
  · simp only [ha0,zero_pow (Nat.ne_of_gt hr)]
    linarith
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hHp : 0 < H := by linarith
  have hNp : 0 < N := by linarith
  have hBp : 0 < B := by linarith
  have hrc : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hkc : (4:ℝ)*r ≤ k := by exact_mod_cast hk
  have hrp : (0:ℝ) < r := by exact_mod_cast hr
  have hkp : (0:ℝ) < k := by linarith
  have hk1 : (1:ℝ) ≤ k := by linarith
  have hlnN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlnB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hln2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlm := Real.log_le_log hap hmoment
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul hHp.ne' (by positivity), Real.log_pow,
    Real.log_div hBp.ne' hNp.ne', Real.log_pow] at hlm
  push_cast at hlm
  have hlu := Real.log_le_log hHp hupper
  rw [Real.log_pow,Real.log_mul (by norm_num) hNp.ne'] at hlu
  push_cast at hlu
  have hls := Real.log_le_log (by positivity : 0 < (2*B)^(8*r)) hsize
  rw [Real.log_pow,Real.log_mul (by norm_num) hBp.ne'] at hls
  push_cast at hls
  have hlt := Real.log_le_log (by norm_num : (0:ℝ) < 1) hthreshold
  rw [Real.log_one,Real.log_mul hNp.ne' (by positivity),Real.log_pow] at hlt
  push_cast at hlt
  have hv : -2*(r:ℝ)*Real.log V ≤ Real.log N/4 := by nlinarith only [hlt]
  have hvk := mul_le_mul_of_nonneg_left hv hkp.le
  have hm := mul_le_mul_of_nonneg_left hlm hrp.le
  have hu := mul_le_mul_of_nonneg_left hlu (show 0 ≤ (r:ℝ)-1 by linarith)
  have hc2 : ((r:ℝ)-1)*((k:ℝ)+1) ≤ 2*(r:ℝ)*k := by nlinarith
  have hc2' := mul_le_mul_of_nonneg_right hc2 hln2
  have hcN : (r:ℝ)-1-3*(k:ℝ)/4 ≤ -(k:ℝ)/2 := by linarith
  have hcN' := mul_le_mul_of_nonneg_right hcN hlnN
  have hs := mul_le_mul_of_nonneg_left hls (show 0 ≤ (k:ℝ)/4 by positivity)
  have hextra := mul_nonneg (show 0 ≤ (r:ℝ)*k by positivity) hlnB
  have hnegative := mul_nonneg (show 0 ≤ (k:ℝ)/4 by positivity) hlnN
  have hfinal : (r:ℝ)*Real.log a ≤ Real.log H := by
    nlinarith only [hm,hvk,hu,hc2',hcN',hs,hextra,hnegative]
  apply (Real.log_le_log_iff (pow_pos hap r) hHp).mp
  simpa only [Real.log_pow] using hfinal

end OrdinarySparseLargeValues

end

end OAI
