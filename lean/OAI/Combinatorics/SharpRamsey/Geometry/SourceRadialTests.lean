import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.SourceScales

namespace OAI

section
namespace SharpLogRamsey.SourceRadialTests
open Filter Real
open scoped Topology
noncomputable section

lemma exp_rat (x y : ℝ) : exp x / exp y = exp (x-y) := by
  rw [Real.exp_sub]

theorem threshold_bounds {σ g a : ℝ} {N : ℕ}
    (hσ : 2 ≤ σ) (hg : 0 ≤ g) (ha : exp (-g/20) ≤ a) (ha2 : a ≤ 2)
    (hN : exp (3*σ/2+g)/2 ≤ (N:ℝ)) :
    let M := ⌈a*(N:ℝ)/exp σ⌉₊
    exp (σ/2+19*g/20)/2 ≤ (M:ℝ) ∧
    (M:ℝ) ≤ 3*(N:ℝ)/exp σ ∧
    exp σ/3 ≤ (N:ℝ)/(M:ℝ) ∧
    (N:ℝ)/(M:ℝ) ≤ exp (σ+g/20) := by
  dsimp only
  let M := ⌈a*(N:ℝ)/exp σ⌉₊
  have hN0 : (0:ℝ) < N := (div_pos (exp_pos _) (by norm_num)).trans_le hN
  have ha0 : 0 < a := (exp_pos _).trans_le ha
  have hl : a*(N:ℝ)/exp σ ≤ (M:ℝ) := Nat.le_ceil _
  have hM0 : (0:ℝ) < M := (div_pos (mul_pos ha0 hN0) (exp_pos _)).trans_le hl
  have hmq : a*(N:ℝ) ≤ (M:ℝ)*exp σ := (div_le_iff₀ (exp_pos _)).mp hl
  have hNq : exp σ ≤ (N:ℝ) := by
    have hh : 2 ≤ exp (σ/2+g) := by linarith [Real.add_one_le_exp (σ/2+g)]
    have he : exp (3*σ/2+g)=exp σ*exp (σ/2+g) := by
      rw [←exp_add]; congr 1; ring
    rw [he] at hN
    nlinarith [exp_pos σ]
  have hlo : exp (σ/2+19*g/20)/2 ≤ (M:ℝ) := by
    calc
      _ = exp (-g/20)*(exp (3*σ/2+g)/2)/exp σ := by
        rw [show exp (-g/20)*(exp (3*σ/2+g)/2)/exp σ =
          (exp (-g/20)*exp (3*σ/2+g)/exp σ)/2 by ring,
          ←exp_add,exp_rat]
        congr 2
        ring
      _  ≤  a*(N:ℝ)/exp σ := by gcongr
      _  ≤  _ := hl
  have hup : (M:ℝ) ≤ 3*(N:ℝ)/exp σ := by
    have hm := Nat.ceil_lt_add_one (show 0 ≤ a*(N:ℝ)/exp σ by positivity)
    change (M:ℝ) < _ at hm
    have hq : 1 ≤ (N:ℝ)/exp σ := (one_le_div (exp_pos _)).mpr hNq
    have hh := mul_le_mul_of_nonneg_right ha2 (div_nonneg hN0.le (exp_pos σ).le)
    rw [←mul_div_assoc] at hh
    calc
      (M:ℝ)  ≤  a*(N:ℝ)/exp σ+1 := hm.le
      _  ≤  2*((N:ℝ)/exp σ)+(N:ℝ)/exp σ := add_le_add hh hq
      _ = _ := by ring
  refine ⟨hlo,hup,?_,?_⟩
  · apply (le_div_iff₀ hM0).mpr
    have hh := (le_div_iff₀ (exp_pos _)).mp hup
    nlinarith
  · apply (div_le_iff₀ hM0).mpr
    have hh := mul_le_mul_of_nonneg_right ha hN0.le
    have hexp : exp (-g/20)*exp (σ+g/20)=exp σ := by
      rw [←exp_add]; congr 1; ring
    have H := mul_le_mul_of_nonneg_right (hh.trans hmq) (exp_pos (σ+g/20)).le
    rw [mul_assoc (M:ℝ),mul_comm (exp σ),←mul_assoc (M:ℝ)] at H
    have hs : exp (-g/20)*(N:ℝ)*exp (σ+g/20)=(N:ℝ)*exp σ := by
      rw [mul_right_comm,hexp]
      ring
    rw [hs] at H
    have H' : (N:ℝ)*exp σ ≤ (exp (σ+g/20)*(M:ℝ))*exp σ := by
      simpa only [mul_comm,mul_left_comm,mul_assoc] using H
    exact (mul_le_mul_iff_left₀ (exp_pos σ)).mp H'

theorem rich_tests {σ g m n kp : ℝ}
    (hg : 100000 ≤ g) (hm : exp (σ/2+19*g/20)/2 ≤ m)
    (hr : n/m ≤ exp (σ+g/20)) (hn : 0 ≤ n)
    (hk : kp ≤ 2*exp (σ+17*g/15)) :
    198*sqrt (n/m) < m ∧ 8*kp ≤ m^2 := by
  have hm0 : 0 < m := (div_pos (exp_pos _) (by norm_num)).trans_le hm
  have hsq : exp (σ+19*g/10) ≤ 4*m^2 := by
    have hh := mul_self_le_mul_self (div_nonneg (exp_pos _).le (by norm_num)) hm
    have he : exp (σ/2+19*g/20)^2=exp (σ+19*g/10) := by
      rw [←exp_nat_mul]; congr 1; norm_num; ring
    nlinarith only [hh,he]
  have he : exp (σ+19*g/10)=exp (σ+g/20)*exp (37*g/20) := by
    rw [←exp_add]; congr 1; ring
  have hc : 4*198^2 < exp (37*g/20) := by linarith [add_one_le_exp (37*g/20)]
  have hprod := mul_lt_mul_of_pos_left hc (exp_pos (σ+g/20))
  have hs := sq_sqrt (div_nonneg hn hm0.le)
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ (198:ℝ)^2 by norm_num)
  have hsmall : 198*sqrt (n/m) < m := by
    rw [he] at hsq
    nlinarith [sqrt_nonneg (n/m)]
  have he' : exp (σ+19*g/10)=exp (σ+17*g/15)*exp (23*g/30) := by
    rw [←exp_add]; congr 1; ring
  have hc' : 64 ≤ exp (23*g/30) := by linarith [add_one_le_exp (23*g/30)]
  have hprod' := mul_le_mul_of_nonneg_left hc' (exp_pos (σ+17*g/15)).le
  rw [he'] at hsq
  exact ⟨hsmall,by nlinarith only [hk,hprod',hsq]⟩

theorem characteristic_test {σ g C r : ℝ}
    (hσ : 2000*exp (C/20) ≤ σ) (hg : g ≤ σ/2+C)
    (hr : r ≤ exp (σ+g/20)) : 33*sqrt r < exp σ := by
  have hc : 33^2*exp (C/20) < exp (39*σ/40) := by
    linarith [add_one_le_exp (39*σ/40),exp_pos (C/20)]
  have hr' : r ≤ exp (41*σ/40)*exp (C/20) := by
    rw [←exp_add]
    exact hr.trans (exp_le_exp.mpr (by linarith))
  have H := mul_lt_mul_of_pos_left hc (exp_pos (41*σ/40))
  have he : exp σ^2=exp (41*σ/40)*exp (39*σ/40) := by
    rw [←exp_nat_mul,←exp_add]; congr 1; norm_num; ring
  have hs : sqrt r^2 ≤ exp (41*σ/40)*exp (C/20) := by
    by_cases h : 0 ≤ r
    · rwa [sq_sqrt h]
    · rw [sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
      simpa only [zero_pow (by decide : (2:ℕ)≠0)] using (le_of_lt (mul_pos (exp_pos (41*σ/40)) (exp_pos (C/20))))
  have h0 := sqrt_nonneg r
  nlinarith [exp_pos σ]

theorem failure_test {σ g C n r : ℝ}
    (_hσ : 2 ≤ σ) (hg : g ≤ σ/2+C) (hn : 0 ≤ n)
    (hn' : n ≤ exp (3*σ/2+g))
    (hr : exp σ/3 ≤ r) (hp : 3*σ^4 ≤ exp σ)
    (hc : 4*σ+2*C-5*σ^2 ≤ -2) :
    n^2*exp (-5*sqrt r) < 1/2 := by
  have hr0 : 0 ≤ r := (div_pos (exp_pos _) (by norm_num)).le.trans hr
  have hs : σ^2 ≤ sqrt r := by
    have hs' := sq_sqrt hr0
    have h0 := sqrt_nonneg r
    nlinarith [sq_nonneg σ]
  have hnn : n^2 ≤ exp (3*σ+2*g) := by
    have hh := mul_self_le_mul_self hn hn'
    have he : exp (3*σ/2+g)^2=exp (3*σ+2*g) := by
      rw [←exp_nat_mul]; congr 1; norm_num; ring
    nlinarith only [hh,he]
  have hh : n^2*exp (-5*sqrt r) ≤ exp (-2) := by
    calc
      _  ≤  exp (3*σ+2*g)*exp (-5*sqrt r) :=
        mul_le_mul_of_nonneg_right hnn (exp_pos _).le
      _ = exp (3*σ+2*g-5*sqrt r) := by rw [←exp_add]; congr 1; ring
      _  ≤  _ := exp_le_exp.mpr (by linarith)
  have he : exp (-2) < 1/2 := by
    rw [exp_neg]
    apply (inv_lt_comm₀ (exp_pos _) (by norm_num)).mpr
    norm_num
    linarith [add_one_le_exp (2:ℝ)]
  exact hh.trans_lt he

end
end SharpLogRamsey.SourceRadialTests

end

end OAI
