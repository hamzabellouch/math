import OAI.NumberTheory.JointDickman.Counting.AuxiliaryExceptionalEnergy
import OAI.NumberTheory.JointDickman.Amplification.ParameterEstimates

namespace OAI

/-! # Scalar bounds for summing the auxiliary logarithmic bins -/
namespace JointDickman
open Filter
open scoped Topology

lemma auxiliary_threshold_bounds {v : ℝ} (hv : 1 ≤ v) :
    ((v^10)⁻¹)^2 ≤ 1 ∧ ((v^10)⁻¹)^2 ≤ 1/v^4 := by
  have hv0 : 0 < v := by linarith
  have hp : v^2 ≤ v^10 := pow_le_pow_right₀ hv (by norm_num)
  have hi : (v^10)⁻¹ ≤ (v^2)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr hp
  constructor
  · have h10 : 1 ≤ v^10 := one_le_pow₀ hv
    have h1 : (v^10)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr h10
    nlinarith [inv_nonneg.mpr (pow_nonneg hv0.le 10)]
  · have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (v^10)⁻¹) hi 2
    simpa only [← inv_pow,← pow_mul,one_div] using hh

lemma auxiliary_frequency_log {X T : ℝ} (hX : 1 ≤ Real.log X)
    (hX0 : 0 < X) (hT : 0 ≤ T) (hTX : T ≤ X) :
    2*(1+Real.log (2*T+1)) ≤ 8*Real.log X := by
  have hX1 : 1 ≤ X := by
    have hh := Real.log_le_sub_one_of_pos hX0
    linarith
  have hl := Real.log_le_log (by linarith : 0<2*T+1)
    (show 2*T+1 ≤ 3*X by linarith)
  rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hX0.ne'] at hl
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  nlinarith

lemma auxiliary_exceptional_power {X a β : ℝ} (hX : 0 < X) (ha : 0 ≤ a)
    (hab : a ≤ X^β) :
    X^(5/12:ℝ)*Real.sqrt (2*X)*a/X ≤ 2*X^(β-1/12) := by
  have hs : Real.sqrt (2*X) ≤ 2*X^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hX.le]
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hX.le _)) hab ha
    (by positivity : 0 ≤ X^(5/12:ℝ)*(2*X^(1/2:ℝ)))
  apply (div_le_div_of_nonneg_right hb hX.le).trans_eq
  calc
    _ = 2*(X^(5/12:ℝ)*X^(1/2:ℝ)*X^β/X) := by ring
    _ = 2*X^(β-1/12) := by
      rw [← Real.rpow_add hX,← Real.rpow_add hX,← Real.rpow_sub_one hX.ne']
      congr 2
      ring

lemma eventually_auxiliary_log_lower {α : ℝ} (hα : 0 < α) :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ, Real.exp (-1)*X^α ≤ a →
      1 ≤ Real.log a ∧ (α/2)*Real.log X ≤ Real.log a := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4/α)),
    eventually_gt_atTop (0:ℝ)] with X hlog hX a ha
  have hprod : 0 < Real.exp (-1)*X^α := by positivity
  have hh := Real.log_le_log hprod ha
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hX _).ne',
    Real.log_exp,Real.log_rpow hX] at hh
  have hlarge := (div_le_iff₀ hα).mp hlog
  constructor <;> nlinarith

end JointDickman

end OAI
