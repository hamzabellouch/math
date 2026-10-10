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
open ArithmeticFunction

namespace OrdinaryMellinModulus
open Filter

lemma quadratic_geometric_limit (A : ℝ) :
    Tendsto (fun n : ℕ => (1+(A+(n:ℝ)+1)^2)*(1/2:ℝ)^n) atTop (nhds 0) := by
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  convert ((h0.const_mul (1+(A+1)^2)).add (h1.const_mul (2*(A+1)))).add h2 using 1
  · ext n
    ring
  · ring_nf

lemma choose_initial_offset (C CT P : ℝ) :
    ∃ c : ℕ, 24*C<(2:ℝ)^c ∧ 8*P<(2:ℝ)^c ∧
      16960*(1+(CT+(c:ℝ)+1)^2)≤(2:ℝ)^c := by
  have hpoly := (quadratic_geometric_limit CT).const_mul 16960
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have hp : ∀ᶠ c : ℕ in atTop,
      16960*(1+(CT+(c:ℝ)+1)^2)*(1/2:ℝ)^c<1 := by
    have he := hpoly.eventually (gt_mem_nhds (by norm_num : 16960*(0:ℝ)<1))
    simpa only [mul_zero,mul_assoc] using he
  obtain ⟨c,⟨hC,hP⟩,hc⟩ := (hpow.eventually_gt_atTop (24*C) |>.and
    (hpow.eventually_gt_atTop (8*P)) |>.and hp).exists
  refine ⟨c,hC,hP,?_⟩
  have he : (1/2:ℝ)^c = 1/(2:ℝ)^c := by rw [one_div_pow]
  rw [he,mul_one_div,div_lt_one (by positivity)] at hc
  exact hc.le

lemma powered_rate (CT : ℝ) (hCT : 0≤CT) (c m : ℕ)
    (hc : 16960*(1+(CT+(c:ℝ)+1)^2)≤(2:ℝ)^c) :
    2120/((2^(3*m+c):ℕ):ℝ) ≤
      ((1/2:ℝ)^m/8)/(1+(CT+((m+c:ℕ):ℝ)*Real.log 2)^2) := by
  have htwo : (1:ℝ)≤(2:ℝ)^m := one_le_pow₀ (by norm_num)
  have hm : (m:ℝ)≤(2:ℝ)^m := by exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n:=m)))
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  let A : ℝ := CT+(c:ℝ)+1
  let L : ℝ := CT+((m+c:ℕ):ℝ)*Real.log 2
  have hA : 0≤A := by dsimp [A]; positivity
  have hL : 0≤L := by dsimp [L]; positivity
  have hLA : L≤A*(2:ℝ)^m := by
    have h1 := mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg (m+c))
    have h2 := mul_le_mul_of_nonneg_left htwo (show 0≤CT+(c:ℝ) by positivity)
    dsimp [L,A]
    push_cast at h1 ⊢
    nlinarith
  have hsquare := pow_le_pow_left₀ hL hLA 2
  have hbudget : 1+L^2 ≤ (1+A^2)*(2:ℝ)^(2*m) := by
    have hp : (1:ℝ)≤((2:ℝ)^m)^2 := one_le_pow₀ htwo
    rw [mul_pow] at hsquare
    rw [mul_comm 2 m,pow_mul]
    nlinarith
  have hfin : 16960*(1+L^2)*(2:ℝ)^m≤(2:ℝ)^(3*m+c) := by
    calc
      _ ≤ 16960*((1+A^2)*(2:ℝ)^(2*m))*(2:ℝ)^m := by gcongr
      _ = (16960*(1+A^2))*(2:ℝ)^(3*m) := by
        rw [show 3*m=2*m+m by omega,pow_add]
        ring
      _ ≤ (2:ℝ)^c*(2:ℝ)^(3*m) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by rw [←pow_add]; congr 1; omega
  have hLp : 0<1+L^2 := by positivity
  have hp : 0<(2:ℝ)^(3*m+c) := by positivity
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  change 2120/(2:ℝ)^(3*m+c) ≤ ((1/2:ℝ)^m/8)/(1+L^2)
  rw [one_div_pow,div_div,div_div]
  apply (div_le_div_iff₀ hp (by positivity)).mpr
  nlinarith only [hfin]

end OrdinaryMellinModulus

end

end OAI
