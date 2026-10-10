import Mathlib

namespace OAI

noncomputable section
namespace SharpRamseyFive.ValidationBounds
open scoped BigOperators Classical
lemma validation_budget_wide {B P L : ℝ} {R : ℕ}
    (hP : 100000 ≤ P) (hR : (R:ℝ) ≤ P/100000)
    (hLR : 100*L ≤ P)
    (D S : ℝ) (hD0 : 0 ≤ D) (hD : D ≤ 100*B*Real.exp (L/100))
    (hS : S ≤ (400*B^2+2*(B^2*Real.exp (P/50)))*2^R) :
    D^2+S ≤ B^2*Real.exp (3*P/100) := by
  have hlog : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hpow : (2:ℝ)^R ≤ Real.exp (P/100000) := by
    rw [show (2:ℝ)^R = Real.exp ((R:ℝ)*Real.log 2) by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]]
    apply Real.exp_le_exp.mpr
    calc
      (R:ℝ)*Real.log 2 ≤ (R:ℝ)*1 := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ P/100000 := by simpa using hR
  have hE : 1 ≤ Real.exp (P/50) := Real.one_le_exp (by linarith)
  have hS' : S ≤ 402*B^2*Real.exp (P/50+P/100000) := by
    calc
      S ≤ (400*B^2+2*(B^2*Real.exp (P/50)))*2^R := hS
      _ ≤ (402*B^2*Real.exp (P/50))*Real.exp (P/100000) := by
        apply mul_le_mul _ hpow (by positivity) (by positivity)
        nlinarith [sq_nonneg B,mul_le_mul_of_nonneg_left hE (sq_nonneg B)]
      _ = _ := by rw [Real.exp_add]; ring
  have hD' : D^2 ≤ 10000*B^2*Real.exp (P/5000) := by
    calc
      _ ≤ (100*B*Real.exp (L/100))^2 := pow_le_pow_left₀ hD0 hD 2
      _ = 10000*B^2*Real.exp (2*(L/100)) := by
        rw [show Real.exp (2*(L/100)) = Real.exp (L/100)^2 by
          simpa using Real.exp_nat_mul (L/100) 2]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hD'' : D^2 ≤ 10000*B^2*Real.exp (P/50+P/100000) := hD'.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity))
  have hcoef : (10402:ℝ) ≤ Real.exp (3*P/100-(P/50+P/100000)) := by
    have ht : (100:ℝ) ≤ 3*P/100-(P/50+P/100000) := by linarith
    have he' : (10402:ℝ) ≤ Real.exp (100:ℝ) := by
      have he2 := Real.add_one_le_exp (25:ℝ)
      have he26 : (26:ℝ) ≤ Real.exp 25 := by linarith
      have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤26) he26 4
      rw [← Real.exp_nat_mul] at hp
      norm_num at hp
      exact (by norm_num : (10402:ℝ)≤456976).trans hp
    exact he'.trans (Real.exp_le_exp.mpr ht)
  calc
    D^2+S ≤ 10402*B^2*Real.exp (P/50+P/100000) := by linarith [hD'',hS']
    _ ≤ Real.exp (3*P/100-(P/50+P/100000))*B^2*Real.exp (P/50+P/100000) := by
      gcongr
    _ = _ := by rw [mul_assoc,mul_left_comm,← Real.exp_add]; congr 2; ring

lemma final_validation_budget_wide {B P L N D S : ℝ} {R : ℕ}
    (hP : 100000≤P) (hL : 1≤L) (hPR : P=L*(R:ℝ))
    (hR : (R:ℝ)≤P/100000) (hlog : (R:ℝ)*Real.log L≤P/100)
    (hN : N≤400*B^2) (hN0 : 0≤N) (hDS : D^2+S≤B^2*Real.exp (3*P/100)) :
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
  have hc : (400:ℝ)≤Real.exp (P/20) := by
    have he := Real.add_one_le_exp (P/20)
    linarith
  have hd : N*(2*Real.exp (-L*(3/4)))^R≤B^2*Real.exp (-69*P/100) := by
    calc
      _ ≤ (400*B^2)*Real.exp (-74*P/100) :=
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

end

end OAI
