import OAI.NumberTheory.ShortEgyptian.RecurrenceUnrolling

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Filter Topology

lemma density_recurrence (S : ℝ) (h : ListScale S) (hm : MomentScale S) (hq : 2 ≤ S^(1/4:ℝ))
    (C : ℕ) (R : ResidueSystem S C) (hClo : Real.exp ((dimC:ℝ)*S) ≤ C)
    (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) (j : ℕ) (hj : j < depth S) :
    levelDensity S R.M C j ≤ Real.exp (-(1/1000:ℝ)*scaleM S)+
      Real.exp (2*S^(1/4:ℝ))*(levelDensity S R.M C (j+1))^descentAlpha := by
  have hh := density_precise_recurrence S h hm C R hClo hChi j hj
  have hd := levelDensity_bounds S R.M C (j+1)
  have hp := Real.self_le_rpow_of_le_one hd.1 hd.2 descentAlpha_bounds.2.le
  have hr : (2:ℝ) ≤ descentR := by exact_mod_cast descentR_ge_two
  have hE : Real.exp (S^(1/4:ℝ)/(descentR:ℝ)) ≤ Real.exp (S^(1/4:ℝ)) :=
    Real.exp_le_exp.mpr (div_le_self (by positivity) (by linarith))
  have h3 : 3 ≤ Real.exp (S^(1/4:ℝ)) := by linarith [Real.add_one_le_exp (S^(1/4:ℝ))]
  have hcoef : 1+2*Real.exp (S^(1/4:ℝ)/(descentR:ℝ)) ≤ Real.exp (2*S^(1/4:ℝ)) := by
    rw [show 2*S^(1/4:ℝ)=S^(1/4:ℝ)+S^(1/4:ℝ) by ring,Real.exp_add]
    nlinarith
  have hp0 : 0 ≤ (levelDensity S R.M C (j+1))^descentAlpha := Real.rpow_nonneg hd.1 _
  have hh' := mul_le_mul_of_nonneg_right hcoef hp0
  have hρ := mul_le_mul_of_nonneg_right (scaleRho_le_one S) hd.1
  nlinarith only [hh,hh',hρ,hp]

lemma alpha_depth (S : ℝ) (h : ListScale S) : S^(-(1/4:ℝ)) ≤ descentAlpha^depth S := by
  have hr : (2:ℝ) ≤ descentR := by exact_mod_cast descentR_ge_two
  have hrp : 0 < (descentR:ℝ) := by linarith
  have hl := log_one_sub_inverse_lower (descentR:ℝ) hr
  change -(2/(descentR:ℝ)) ≤ Real.log descentAlpha at hl
  have hd := depth_bound S h.S_pos h.log_one h.m_bounds.1 h.m_bounds.2.2
  have heq : (descentR:ℝ)=8*(3*(dimX:ℝ)*10000) := by rw [descentR_eq]; push_cast; ring
  have hcoef : (2*(depth S:ℝ))/(descentR:ℝ) ≤ (1/4:ℝ)*Real.log S := by
    apply (div_le_iff₀ hrp).mpr
    rw [heq]
    nlinarith
  rw [Real.rpow_def_of_pos h.S_pos]
  have hp : descentAlpha^depth S = Real.exp ((depth S:ℝ)*Real.log descentAlpha) := by
    rw [Real.exp_nat_mul,Real.exp_log descentAlpha_bounds.1]
  rw [hp]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (depth S) : (0:ℝ) ≤ depth S)
  rw [show (depth S:ℝ)*-(2/(descentR:ℝ)) = -(2*(depth S:ℝ)/(descentR:ℝ)) by ring] at hh
  linarith

lemma density_unrolled (S : ℝ) (h : ListScale S) (hm : MomentScale S) (hq : 2 ≤ S^(1/4:ℝ))
    (C : ℕ) (R : ResidueSystem S C) (hClo : Real.exp ((dimC:ℝ)*S) ≤ C)
    (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) :
    levelDensity S R.M C 0 ≤ (depth S:ℝ)*Real.exp
      (2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ))) := by
  have hrp : 0 < (descentR:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<2) descentR_ge_two)
  have hfix : 2*S^(1/4:ℝ)+(2*(descentR:ℝ)*S^(1/4:ℝ))*descentAlpha=2*(descentR:ℝ)*S^(1/4:ℝ) := by
    dsimp [descentAlpha]
    field_simp
    ring
  have hh := backwards_recurrence_bound (levelDensity S R.M C) (depth S) descentAlpha
    (2*S^(1/4:ℝ)) (2*(descentR:ℝ)*S^(1/4:ℝ)) ((1/1000:ℝ)*scaleM S)
    descentAlpha_bounds.1 descentAlpha_bounds.2.le (by positivity) (by positivity) hfix
    (fun j => (levelDensity_bounds S R.M C j).1) (levelDensity_last S h C R)
    (fun j hj => by simpa only [neg_mul] using density_recurrence S h hm hq C R hClo hChi j hj)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  have ha := mul_le_mul_of_nonneg_left (alpha_depth S h) (show (0:ℝ) ≤ (1/1000:ℝ)*scaleM S by positivity)
  linarith

lemma eventually_density_numeric : ∀ᶠ S : ℝ in atTop,
    (depth S:ℝ)*Real.exp (2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ))) ≤ 1/8 := by
  let B : ℝ := 1000*(2*(descentR:ℝ)+2)
  let K : ℝ := 3*(dimX:ℝ)*10000
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := by dsimp [K]; norm_num [dimX,dimM]
  filter_upwards [eventually_ListScale,eventually_log_pow_le (2*B) 1 (by norm_num : (0:ℝ)<1/2),
    eventually_log_pow_le 1 1 (by norm_num : (0:ℝ)<1/4),eventually_ge_atTop (8*K)] with S h hnum hlog hS
  simp only [pow_one,one_mul] at hnum hlog
  have hp : 0 < S^(1/2:ℝ) := Real.rpow_pos_of_pos h.S_pos _
  have hlo : 0 < Real.log S := by linarith [h.log_one]
  have heq : S^(1/2:ℝ)*S^(1/2:ℝ)=S := by rw [←Real.rpow_add h.S_pos]; norm_num
  have hm : B*S^(1/2:ℝ) ≤ (scaleM S:ℝ) := by
    apply le_trans _ h.m_bounds.1
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*Real.log S)).mpr
    have hh := mul_le_mul_of_nonneg_right hnum hp.le
    rw [heq] at hh
    nlinarith [mul_nonneg hB.le hp.le]
  have heq' : S^(1/2:ℝ)*S^(-(1/4:ℝ))=S^(1/4:ℝ) := by rw [←Real.rpow_add h.S_pos]; norm_num
  have hmm := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg h.S_pos.le (-(1/4:ℝ)))
  rw [mul_assoc,heq'] at hmm
  have hneg : 2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ)) ≤ -(2*Real.log S) := by
    dsimp [B] at hmm
    nlinarith
  have hE : Real.exp (2*(descentR:ℝ)*S^(1/4:ℝ)-(1/1000:ℝ)*scaleM S*S^(-(1/4:ℝ))) ≤ 1/S^2 := by
    calc
      _ ≤ Real.exp (-(2*Real.log S)) := Real.exp_le_exp.mpr hneg
      _ = _ := by rw [Real.exp_neg,two_mul,Real.exp_add,Real.exp_log h.S_pos]; simp [pow_two]
  have hd := depth_bound S h.S_pos h.log_one h.m_bounds.1 h.m_bounds.2.2
  have hLS : Real.log S ≤ S := by linarith [Real.log_le_sub_one_of_pos h.S_pos]
  calc
    _ ≤ (K*S)*(1/S^2) := mul_le_mul (hd.trans (mul_le_mul_of_nonneg_left hLS hK.le)) hE (Real.exp_nonneg _) (mul_nonneg hK.le h.S_pos.le)
    _ = K/S := by field_simp
    _ ≤ _ := (div_le_iff₀ h.S_pos).mpr (by linarith)

end ShortEgyptian

end OAI
