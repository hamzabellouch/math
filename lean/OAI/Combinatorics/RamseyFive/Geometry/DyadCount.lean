import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Beta

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open Filter Asymptotics ParameterHierarchy
open scoped Topology

lemma dyad_count_le {m : ℕ} {σ : ℝ} (hσ : 1≤σ)
    (hm : (m:ℝ)≤Real.exp (3*σ)) : (Nat.clog 2 m:ℝ)+1≤8*σ := by
  by_cases hm1 : m≤1
  · rw [Nat.clog_of_right_le_one hm1]
    simp only [Nat.cast_zero,zero_add]
    linarith
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hml : 0≤Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hlog2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmlhi : Real.log (m:ℝ)≤3*σ := (Real.log_le_iff_le_exp hm0).mpr hm
  have hlog : Real.logb 2 (m:ℝ)≤6*σ := by
    rw [Real.logb]
    apply (div_le_iff₀ (by linarith : 0<Real.log 2)).mpr
    nlinarith
  have hc := Nat.ceil_lt_add_one (show 0≤Real.logb 2 (m:ℝ) by
    rw [Real.logb]; exact div_nonneg hml (by linarith))
  have he := Real.natCeil_logb_natCast 2 m
  norm_num only [Nat.cast_ofNat] at he
  rw [he] at hc
  linarith

theorem eventually_global_trunc_scalar {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (C : ℝ) (hC : 0<C) :
    ∀ᶠ σ : ℝ in atTop,∀ D R g : ℝ,Range η σ D R → P η σ D R/10000≤g →
      C*(P η σ D R)^5000*Real.exp (8*σ-250*(g+σ/2))+
        C*(P η σ D R)^5000*σ*Real.exp (2*σ-4998*g)≤Real.exp (2*σ) := by
  have habs := eventually_power_absorption hη hη' (2*C) 5001 (1/10)
    (by positivity) (by norm_num) (by norm_num)
  have hsmall := eventually_hierarchy hη hη' 0 1 0 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),habs,hsmall] with σ hσ habs hsmall
  intro D R g hr hg
  have hpar := finite_bounds hη hη' hσ hr
  have hD := hpar.1
  have hL : 0<L η σ D := by dsimp [L]; positivity
  have hP : 0<P η σ D R := mul_pos hL hpar.2.1
  have hPσ : P η σ D R≤σ := by
    have hh := hsmall D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
    simpa only [one_mul] using hh.2.1
  have hg0 : 0≤g := (by positivity : 0≤P η σ D R/10000).trans hg
  have hab : 2*C*σ^(5001:ℕ)≤Real.exp (P η σ D R/10) := by
    have hh := habs D R hr
    rw [show σ^(5001:ℝ)=σ^(5001:ℕ) from Real.rpow_natCast σ 5001] at hh
    simpa only [one_div,one_mul,mul_comm (10⁻¹:ℝ),div_eq_mul_inv] using hh
  have hpow : (P η σ D R)^5000≤σ^5000 := pow_le_pow_left₀ hP.le hPσ _
  have hcoeff2 : 2*(C*(P η σ D R)^5000*σ)≤Real.exp (P η σ D R/10) := by
    calc
      _ = 2*C*(P η σ D R)^5000*σ := by ring
      _ ≤ 2*C*σ^5000*σ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (by linarith)
      _ = 2*C*σ^5001 := by rw [pow_succ]; ring
      _ ≤ _ := hab
  have hcoeff1 : 2*(C*(P η σ D R)^5000)≤Real.exp (P η σ D R/10) := by
    apply le_trans _ hcoeff2
    nlinarith [mul_nonneg (by positivity : 0≤C*(P η σ D R)^5000) (sub_nonneg.mpr hσ)]
  have h1 : 2*(C*(P η σ D R)^5000*Real.exp (8*σ-250*(g+σ/2)))≤Real.exp (2*σ) := by
    calc
      _ = (2*(C*(P η σ D R)^5000))*Real.exp (8*σ-250*(g+σ/2)) := by ring
      _ ≤ Real.exp (P η σ D R/10)*Real.exp (8*σ-250*(g+σ/2)) :=
        mul_le_mul_of_nonneg_right hcoeff1 (Real.exp_nonneg _)
      _ = Real.exp (P η σ D R/10+(8*σ-250*(g+σ/2))) := (Real.exp_add ..).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have h2 : 2*(C*(P η σ D R)^5000*σ*Real.exp (2*σ-4998*g))≤Real.exp (2*σ) := by
    calc
      _ = (2*(C*(P η σ D R)^5000*σ))*Real.exp (2*σ-4998*g) := by ring
      _ ≤ Real.exp (P η σ D R/10)*Real.exp (2*σ-4998*g) :=
        mul_le_mul_of_nonneg_right hcoeff2 (Real.exp_nonneg _)
      _ = Real.exp (P η σ D R/10+(2*σ-4998*g)) := (Real.exp_add ..).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  linarith

end SharpRamseyFive.ScoreGeometry

end

end OAI
