import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

namespace SKGap.DiscreteRecurrence
open Real

lemma affine_upper (u : ℕ→ℝ) {b r : ℝ} (hb : 0≤b) (hr : 0≤r)
    (hzero : u 0≤0) (K : ℕ)
    (hstep : ∀k<K,u (k+1)≤(1+b)*u k+r) :
    u K≤(K:ℝ)*r*exp ((K:ℝ)*b) := by
  have hh : ∀ k≤K,u k≤(k:ℝ)*r*(1+b)^k := by
    intro k hk
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
      have hi:=mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hk)) (by linarith : 0≤1+b)
      have hp : 1≤(1+b)^(k+1) := one_le_pow₀ (by linarith)
      have hrp:=mul_le_mul_of_nonneg_left hp hr
      have hs:=hstep k (Nat.lt_of_succ_le hk)
      simp only [Nat.cast_add,Nat.cast_one,pow_succ] at hrp ⊢
      nlinarith
  have hp:=pow_le_pow_left₀ (by linarith : 0≤1+b) (by simpa only [add_comm] using Real.add_one_le_exp b) K
  have hm:=mul_le_mul_of_nonneg_left hp (show 0≤(K:ℝ)*r by positivity)
  rw [←Real.exp_nat_mul] at hm
  simpa only [mul_comm b] using (hh K le_rfl).trans hm

lemma affine_lower (u : ℕ→ℝ) {r b : ℝ} (hr : 0≤r) (hr1 : r≤1) (hb : 0≤b)
    (K : ℕ) (hstep : ∀k<K,r*u k-b≤u (k+1)) :
    r^K*u 0-(K:ℝ)*b≤u K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hi:=mul_le_mul_of_nonneg_left (ih (fun k hk => hstep k (hk.trans (Nat.lt_succ_self K)))) hr
    have hs:=hstep K (Nat.lt_succ_self K)
    have hb':=mul_le_mul_of_nonneg_right hr1 (show 0≤(K:ℝ)*b by positivity)
    rw [Nat.cast_add,Nat.cast_one,pow_succ]
    nlinarith

lemma exp_neg_two_le {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) :
    exp (-2*x)≤1-x := by
  have hpos : 0<1-x := by linarith
  have hi : (1-x)⁻¹≤1+2*x := by
    rw [inv_eq_one_div,div_le_iff₀ hpos]
    nlinarith
  have hl:=Real.one_sub_inv_le_log_of_pos hpos
  have hh : -2*x≤log (1-x) := by linarith
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hh

lemma pow_one_sub_lower {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) (K : ℕ) :
    exp (-2*(K:ℝ)*x)≤(1-x)^K := by
  have hh:=pow_le_pow_left₀ (exp_pos (-2*x)).le (exp_neg_two_le hx hx1) K
  rw [←Real.exp_nat_mul] at hh
  have he : (K:ℝ)*(-2*x)= -2*(K:ℝ)*x := by ring
  rwa [he] at hh

end SKGap.DiscreteRecurrence

end OAI
