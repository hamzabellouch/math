import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.StageNumerics
import OAI.Combinatorics.RamseyFive.Entropy.WindowBudgetNumerics

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking ProjectiveIncidence
open scoped Topology
noncomputable section
lemma log_length_three {σ q η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (hσ : 6≤σ) (hq : Real.exp σ=q) (l : ℕ) (hl : (l:ℝ)≤q*σ^(1+η)) :
    Real.log (l+1)≤3*σ := by
  have hp : 0<σ := by linarith
  have hσ1 : 1≤σ := by linarith
  have hpow : σ^(1+η)≤σ^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hσ1 (by linarith)
  have hexp : σ^2≤Real.exp σ := by
    have hh:=Real.pow_div_factorial_le_exp σ hp.le 3
    norm_num only [Nat.factorial] at hh
    have hs3 : σ^2≤σ^3/6 := by nlinarith [mul_nonneg (sq_nonneg σ) (show 0≤σ-6 by linarith)]
    exact hs3.trans hh
  have hlen : (l:ℝ)≤q*q := hl.trans (mul_le_mul_of_nonneg_left (hpow.trans (hexp.trans_eq hq)) (by rw [←hq];positivity))
  have hq1 : 1≤q := by rw [←hq];exact Real.one_le_exp hp.le
  have hsum : (l:ℝ)+1≤2*(q*q) := by nlinarith
  have hh:=Real.log_le_log (by positivity : (0:ℝ)<(l:ℝ)+1) hsum
  have hqp : 0<q := by rw [←hq];positivity
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (mul_pos hqp hqp).ne',Real.log_mul hqp.ne' hqp.ne',←hq,Real.log_exp] at hh
  have hlog2 : Real.log 2≤1 := by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  linarith

lemma prescribed_P_bounds {η σ D R : ℝ} (hη : 0<η) (hσ : 1≤σ) (hR : Range η σ D R) :
    D*σ^(9*beta η)≤P η σ D R ∧ P η σ D R≤4*D*σ^(9*beta η) := by
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hb:=beta_pos hη
  have hx : 1≤σ^beta η := Real.one_le_rpow hσ hb.le
  have hD : 0≤D := (Real.rpow_nonneg hp.le _).trans hR.dlo
  have hRh : R≤4*σ^beta η := hR.rhi.trans (by linarith)
  have heq : D*σ^(8*beta η)*σ^beta η=D*σ^(9*beta η) := by
    rw [mul_assoc,←Real.rpow_add hp];congr 2;ring
  constructor
  · rw [←heq]
    exact mul_le_mul_of_nonneg_left hR.rlo (by positivity)
  · calc
      _ ≤D*σ^(8*beta η)*(4*σ^beta η) := mul_le_mul_of_nonneg_left hRh (by positivity)
      _ =4*(D*σ^(8*beta η)*σ^beta η) := by ring
      _ =_ := by rw [heq];ring

theorem eventually_reciprocal_code_budget {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (q D R k : ℝ) (w H l : ℕ),
      Real.exp σ=q→Range η σ D R→1≤H→(H:ℝ)≤σ^beta η→
      (w:ℝ)*D≤σ^(1+η/2)→q*σ^(1+η)≤2*k→(l:ℝ)≤q*σ^(1+η)→
      windowCodeBudget σ q (P η σ D R) (D*σ^(6*beta η)+2*(D*σ^(2*beta η))+Real.log 4) w H+
          (w+1)*Real.log (l+1)≤k*D*σ^(-η/3) := by
  have hb:=beta_pos hη
  have h3 : 0<3*beta η := by positivity
  have hm : 0≤8+7*nodeChargeConstant := by have:=nodeChargeConstant_nonneg;positivity
  filter_upwards [eventually_ge_atTop (6:ℝ),
    (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (max 1 (2*Real.log (320/(9/100000)+320)))),
    (tendsto_rpow_atTop h3).eventually (eventually_ge_atTop (3+Real.log 4)),
    eventually_stage_entropy_bound hη (8+7*nodeChargeConstant) 1 hm (by norm_num)] with σ hσ hg hg3 hbudget
  intro q D R k w H l hq hr hH hHhi hw hk hl
  have hσ1 : 1≤σ := by linarith
  have hp : 0<σ := by linarith
  have hqp : 0<q := by rw [←hq];positivity
  have hD : 0<D := (Real.rpow_pos_of_pos hp _).trans_le hr.dlo
  obtain ⟨hPlo,hPhi⟩:=prescribed_P_bounds hη hσ1 hr
  have hD1 : 1≤D := (Real.one_le_rpow hσ1 hb.le).trans hr.dlo
  have hP1 : 1≤P η σ D R := by
    have hh:=Real.one_le_rpow hσ1 (show 0≤9*beta η by positivity)
    nlinarith
  have hPmeta : 2*Real.log (320/(9/100000)+320)≤P η σ D R := by
    have hh : σ^beta η≤σ^(9*beta η) := Real.rpow_le_rpow_of_exponent_le hσ1 (by linarith)
    have hh' : σ^(9*beta η)≤D*σ^(9*beta η) := le_mul_of_one_le_left (by positivity) hD1
    exact (le_max_right _ _).trans (hg.trans (hh.trans (hh'.trans hPlo)))
  have hbP : D*σ^(6*beta η)+2*(D*σ^(2*beta η))+Real.log 4≤P η σ D R := by
    have h26 : σ^(2*beta η)≤σ^(6*beta η) := Real.rpow_le_rpow_of_exponent_le hσ1 (by linarith)
    have hk1 : 1≤D*σ^(6*beta η) := by
      have hh:=Real.one_le_rpow hσ1 (show 0≤6*beta η by positivity)
      nlinarith
    have hld : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
    calc
      _ ≤(3+Real.log 4)*(D*σ^(6*beta η)) := by nlinarith [mul_le_mul_of_nonneg_left h26 hD.le]
      _ ≤σ^(3*beta η)*(D*σ^(6*beta η)) := mul_le_mul_of_nonneg_right hg3 (by positivity)
      _ =D*σ^(9*beta η) := by
        rw [mul_left_comm,←Real.rpow_add hp];congr 2;ring
      _ ≤_ := hPlo
  have hlog:=log_length_three hη hη' hσ hq l hl
  have hlog4 : Real.log 4≤σ := by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    linarith
  have hσq : σ≤q := by
    rw [←hq]
    linarith [Real.add_one_le_exp σ]
  have hcoarse:=windowCodeBudget_coarse (w:=w) hσ1 hσq hP1 hH hbP hPmeta hlog4 (by norm_num : (0:ℝ)≤3) hlog
  have hh:=hbudget q D (P η σ D R) H w k _ hqp hD.le (by linarith) (by positivity) (by positivity)
    hPhi hHhi (by simpa only [mul_comm,one_mul] using hw) hk (by simpa only [show (5:ℝ)+7*nodeChargeConstant+3=8+7*nodeChargeConstant by ring] using hcoarse)
  have hkp : 0<k := by have := mul_pos hqp (Real.rpow_pos_of_pos hp (1+η));linarith
  exact (div_le_iff₀ hkp).mp hh |>.trans_eq (by ring)
end
end SharpRamseyFive.ParameterHierarchy

end OAI
