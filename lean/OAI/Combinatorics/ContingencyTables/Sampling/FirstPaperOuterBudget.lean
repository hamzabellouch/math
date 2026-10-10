import OAI.Combinatorics.ContingencyTables.Parameters
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! # The first paper's explicit trial and approximation budgets -/

namespace ContingencyTables

def outerTrials (d k : ℕ) : ℕ := d^4*(k+1)
def outerSteps (d b k : ℕ) : ℕ := d^200*(k+b)^2
def outerAccuracy (d b k : ℕ) : ℕ := d^4*(k+b)^2

lemma two_pow_le_exp_nat (n : ℕ) : (2:ℝ)^n ≤ Real.exp (n:ℝ) := by
  have hbase : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  simpa only [← Real.exp_nat_mul,mul_one] using pow_le_pow_left₀ (by norm_num) hbase n

lemma exp_neg_nat_le_inverse_two_pow (n : ℕ) :
    Real.exp (-(n:ℝ)) ≤ 1/(2:ℝ)^n := by
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity) (two_pow_le_exp_nat n)

lemma outer_failure_error (d k : ℕ) (hd : 14 ≤ d) :
    Real.exp (-(outerTrials d k:ℝ)/(2*(1+(d:ℝ)^2))) ≤ 1/(2:ℝ)^(k+2) := by
  have hdR : (14:ℝ) ≤ d := by exact_mod_cast hd
  have hsq : (196:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hc : 4*(1+(d:ℝ)^2) ≤ (d:ℝ)^4 := by nlinarith [sq_nonneg ((d:ℝ)^2-2)]
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ (k:ℝ)+1 by positivity)
  have ht : (k:ℝ)+2 ≤ (outerTrials d k:ℝ)/(2*(1+(d:ℝ)^2)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    dsimp only [outerTrials]
    push_cast
    nlinarith [mul_nonneg (show (0:ℝ) ≤ k by positivity) (show 0 ≤ 1+(d:ℝ)^2 by positivity)]
  exact (Real.exp_le_exp.mpr (by
    rw [neg_div]
    push_cast
    exact neg_le_neg ht)).trans (exp_neg_nat_le_inverse_two_pow (k+2))

lemma outer_mixing_error (d b k C : ℕ) (hd : 14 ≤ d) (hb : d ≤ b) (hk : 1 ≤ k)
    (hC : C+1 ≤ 2^b) :
    (outerTrials d k:ℝ)*((C+1:ℕ):ℝ)^(2*d)*
      Real.exp (-(outerSteps d b k:ℝ)/(d:ℝ)^160) ≤ 1/(2:ℝ)^(k+2) := by
  let t : ℝ := (k:ℝ)+b
  have ht : 15 ≤ t := by dsimp only [t]; exact_mod_cast (show 15 ≤ k+b by omega)
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdt : (d:ℝ) ≤ t := by dsimp only [t]; exact_mod_cast (show d ≤ k+b by omega)
  have hbt : (b:ℝ) ≤ t := by dsimp only [t]; linarith [Nat.cast_nonneg k (α := ℝ)]
  have hkt : (k:ℝ) ≤ t := by dsimp only [t]; linarith [Nat.cast_nonneg b (α := ℝ)]
  have hde : (d:ℝ) ≤ Real.exp (d:ℝ) := by linarith [Real.add_one_le_exp (d:ℝ)]
  have hke : (k:ℝ)+1 ≤ Real.exp ((k:ℝ)+1) := by
    linarith [Real.add_one_le_exp ((k:ℝ)+1)]
  have hJ : (outerTrials d k:ℝ) ≤ Real.exp (4*(d:ℝ)+k+1) := by
    calc
      _ = (d:ℝ)^4*((k:ℝ)+1) := by simp only [outerTrials,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
      _ ≤ (Real.exp (d:ℝ))^4*Real.exp ((k:ℝ)+1) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hde 4) hke (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul,← Real.exp_add]; congr 1; norm_num; ring
  have hCe : (C+1:ℕ) ≤ Real.exp (b:ℝ) :=
    (show ((C+1:ℕ):ℝ) ≤ (2:ℝ)^b by exact_mod_cast hC).trans (two_pow_le_exp_nat b)
  have hCP : (((C+1:ℕ):ℝ))^(2*d) ≤ Real.exp (2*(d:ℝ)*b) := by
    calc
      _ ≤ (Real.exp (b:ℝ))^(2*d) := pow_le_pow_left₀ (by positivity) hCe _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hcoef : (3:ℝ) ≤ (d:ℝ)^40 := by
    exact_mod_cast ((show 3 ≤ d by omega).trans (Nat.le_self_pow (by decide) d))
  have hdb : (d:ℝ)*b ≤ t^2 := by
    have hh := mul_le_mul hdt hbt (by positivity : (0:ℝ) ≤ b) (by linarith : 0 ≤ t)
    nlinarith
  have hexp : 4*(d:ℝ)+k+1+2*(d:ℝ)*b+((k:ℝ)+2) ≤ (d:ℝ)^40*t^2 := by
    have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
    nlinarith
  calc
    _ ≤ Real.exp (4*(d:ℝ)+k+1)*Real.exp (2*(d:ℝ)*b)*
        Real.exp (-(outerSteps d b k:ℝ)/(d:ℝ)^160) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hJ hCP (by positivity) (by positivity)) (by positivity)
    _ = Real.exp (4*(d:ℝ)+k+1+2*(d:ℝ)*b-(d:ℝ)^40*t^2) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      dsimp only [outerSteps,t]
      push_cast
      field_simp
      ring
    _ ≤ Real.exp (-((k+2:ℕ):ℝ)) := Real.exp_le_exp.mpr (by push_cast; linarith)
    _ ≤ _ := exp_neg_nat_le_inverse_two_pow (k+2)

lemma nat_pow_le_two_pow (n a : ℕ) : n^a ≤ 2^(n*a) := by
  calc
    _ ≤ (2^n)^a := Nat.pow_le_pow_left n.lt_two_pow_self.le a
    _ = _ := (pow_mul _ _ _).symm

lemma outer_product_bit_bound (d b k : ℕ) (hd : 14 ≤ d) (hb : d ≤ b) (hk : 1 ≤ k) :
    outerTrials d k*(outerSteps d b k+1)*2^(k+2) ≤ 2^(outerAccuracy d b k) := by
  let t := k+b
  have ht : 15 ≤ t := by dsimp only [t]; omega
  have hpT : 1 ≤ outerSteps d b k := by
    dsimp only [outerSteps]
    have hd0 : 0 < d := by omega
    have ht0 : 0 < k+b := by omega
    exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos hd0 _) (pow_pos ht0 _))
  have hJ : outerTrials d k ≤ 2^(4*d+k+1) := by
    unfold outerTrials
    calc
      _ ≤ 2^(d*4)*2^(k+1) := Nat.mul_le_mul (nat_pow_le_two_pow d 4) (k+1).lt_two_pow_self.le
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hT : outerSteps d b k+1 ≤ 2^(200*d+2*t+1) := by
    have hm : outerSteps d b k ≤ 2^(200*d+2*t) := by
      unfold outerSteps
      calc
        _ ≤ 2^(d*200)*2^((k+b)*2) := Nat.mul_le_mul (nat_pow_le_two_pow d 200)
          (nat_pow_le_two_pow (k+b) 2)
        _ = _ := by rw [← pow_add]; congr 1; dsimp only [t]; omega
    calc
      _ ≤ 2*outerSteps d b k := by omega
      _ ≤ 2*2^(200*d+2*t) := Nat.mul_le_mul_left 2 hm
      _ = _ := by rw [pow_succ]; omega
  have hexp : (4*d+k+1)+(200*d+2*t+1)+(k+2) ≤ outerAccuracy d b k := by
    have hcoef : 209 ≤ d^4 := (by norm_num : 209 ≤ 14^4).trans (Nat.pow_le_pow_left hd 4)
    have htq : t ≤ t^2 := Nat.le_self_pow (by decide) t
    have hm := Nat.mul_le_mul hcoef htq
    have hdt : d ≤ t := by dsimp only [t]; omega
    have hkt : k ≤ t := by dsimp only [t]; omega
    change _ ≤ d^4*t^2
    omega
  calc
    _ ≤ (2^(4*d+k+1)*2^(200*d+2*t+1))*2^(k+2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hJ hT)
    _ = 2^((4*d+k+1)+(200*d+2*t+1)+(k+2)) := by rw [← pow_add,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

lemma outer_approximation_error (d b k : ℕ) (hd : 14 ≤ d) (hb : d ≤ b) (hk : 1 ≤ k) :
    (outerTrials d k:ℝ)*(outerSteps d b k+1)/(2:ℝ)^(outerAccuracy d b k) ≤
      1/(2:ℝ)^(k+2) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simp only [one_mul]
  exact_mod_cast outer_product_bit_bound d b k hd hb hk

theorem outer_total_error (d b k C : ℕ) (hd : 14 ≤ d) (hb : d ≤ b) (hk : 1 ≤ k)
    (hC : C+1 ≤ 2^b) :
    Real.exp (-(outerTrials d k:ℝ)/(2*(1+(d:ℝ)^2)))+
      (outerTrials d k:ℝ)*((C+1:ℕ):ℝ)^(2*d)*
        Real.exp (-(outerSteps d b k:ℝ)/(d:ℝ)^160)+
      (outerTrials d k:ℝ)*(outerSteps d b k+1)/(2:ℝ)^(outerAccuracy d b k) ≤
      1/(2:ℝ)^k := by
  have h₁ := outer_failure_error d k hd
  have h₂ := outer_mixing_error d b k C hd hb hk hC
  have h₃ := outer_approximation_error d b k hd hb hk
  have he : 4*(1/(2:ℝ)^(k+2))=1/(2:ℝ)^k := by
    rw [pow_add]
    norm_num
    field_simp
  have hp : 0 ≤ 1/(2:ℝ)^(k+2) := by positivity
  linarith

end ContingencyTables

end OAI
