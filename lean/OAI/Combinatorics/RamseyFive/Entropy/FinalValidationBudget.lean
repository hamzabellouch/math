import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ValidationBounds
open scoped BigOperators Classical

lemma final_validation_budget {B P L N D S : ℝ} {R : ℕ}
    (hP : 100000≤P) (hL : 1≤L) (hPR : P=L*(R:ℝ))
    (hR : (R:ℝ)≤P/100000) (hlog : (R:ℝ)*Real.log L≤P/100)
    (hN : N≤100*B^2) (hN0 : 0≤N) (hDS : D^2+S≤B^2*Real.exp (3*P/100)) :
    N*(2*Real.exp (-L*(3/4)))^R+
      (2*L^2*Real.exp (-L*(3/4)))^R*(D^2+S) ≤ B^2*Real.exp (-3*P/5) := by
  have hL0 : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hlog2 : Real.log 2≤1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have he1 : (2*Real.exp (-L*(3/4)))^R=
      Real.exp ((R:ℝ)*Real.log 2-3*P/4) := by
    rw [hPR]
    have hx : (R:ℝ)*Real.log 2-3*(L*(R:ℝ))/4=(R:ℝ)*(Real.log 2+(-L*(3/4))) := by ring
    rw [hx,Real.exp_nat_mul,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have he2 : (2*L^2*Real.exp (-L*(3/4)))^R=
      Real.exp ((R:ℝ)*Real.log 2+2*((R:ℝ)*Real.log L)-3*P/4) := by
    rw [hPR]
    have hx : (R:ℝ)*Real.log 2+2*((R:ℝ)*Real.log L)-3*(L*(R:ℝ))/4=
        (R:ℝ)*(Real.log 2+((2:ℕ):ℝ)*Real.log L+(-L*(3/4))) := by ring
    rw [hx,Real.exp_nat_mul,Real.exp_add,Real.exp_add,Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0:ℝ)<2),Real.exp_log hL0]
  have hh : (R:ℝ)*Real.log 2≤P/100000 := by
    exact (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg R)).trans (by simpa using hR)
  have hp1 : (2*Real.exp (-L*(3/4)))^R≤Real.exp (-74*P/100) := by
    rw [he1]
    exact Real.exp_le_exp.mpr (by linarith)
  have hp2 : (2*L^2*Real.exp (-L*(3/4)))^R≤Real.exp (-72*P/100) := by
    rw [he2]
    exact Real.exp_le_exp.mpr (by linarith)
  have hc : (100:ℝ)≤Real.exp (P/20) := by
    have he := Real.add_one_le_exp (P/20)
    linarith
  have hd : N*(2*Real.exp (-L*(3/4)))^R≤B^2*Real.exp (-69*P/100) := by
    calc
      _ ≤ (100*B^2)*Real.exp (-74*P/100) :=
        mul_le_mul hN hp1 (by positivity) (hN0.trans hN)
      _ ≤ (Real.exp (P/20)*B^2)*Real.exp (-74*P/100) := by gcongr
      _ = B^2*(Real.exp (P/20)*Real.exp (-74*P/100)) := by ring
      _ = B^2*Real.exp (P/20+(-74*P/100)) := by rw [Real.exp_add]
      _ = _ := by congr 2; ring
  have ho : (2*L^2*Real.exp (-L*(3/4)))^R*(D^2+S)≤B^2*Real.exp (-69*P/100) := by
    calc
      _ ≤ (2*L^2*Real.exp (-L*(3/4)))^R*(B^2*Real.exp (3*P/100)) :=
        mul_le_mul_of_nonneg_left hDS (by positivity)
      _ ≤ Real.exp (-72*P/100)*(B^2*Real.exp (3*P/100)) :=
        mul_le_mul_of_nonneg_right hp2 (by positivity)
      _ = B^2*(Real.exp (-72*P/100)*Real.exp (3*P/100)) := by ring
      _ = B^2*Real.exp (-72*P/100+3*P/100) := by rw [Real.exp_add]
      _ = _ := by congr 2; ring
  have htwo : (2:ℝ)≤Real.exp (9*P/100) := by
    have he := Real.add_one_le_exp (9*P/100)
    linarith
  calc
    _ ≤ 2*(B^2*Real.exp (-69*P/100)) := by linarith only [hd,ho]
    _ ≤ Real.exp (9*P/100)*(B^2*Real.exp (-69*P/100)) :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = B^2*(Real.exp (9*P/100)*Real.exp (-69*P/100)) := by ring
    _ = B^2*Real.exp (9*P/100+(-69*P/100)) := by rw [Real.exp_add]
    _ = _ := by congr 2; ring

end SharpRamseyFive.ValidationBounds

end OAI
