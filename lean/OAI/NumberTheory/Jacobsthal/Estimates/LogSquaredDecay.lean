import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.LogSquaredDecay

open Filter
open scoped Topology

lemma power_exponential_saving {c : ℝ} (hc : 0<c) (p A : ℝ) : ∀ᶠ B : ℝ in atTop,
    B^p * Real.exp (-c*((Real.log B)^2/2)) ≤ B^(-A) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2*(A+p)/c)))] with B hB hL
  have hB0 : 0<B := by linarith
  have hL0 : 0≤Real.log B := le_trans zero_le_one ((le_max_left _ _).trans hL)
  have ht : 2*(A+p)≤Real.log B*c := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hL)
  have hm := mul_le_mul_of_nonneg_right ht hL0
  have he : Real.log B*p + (-c*((Real.log B)^2/2)) ≤ Real.log B*(-A) := by nlinarith
  calc
    _ = Real.exp (Real.log B*p + (-c*((Real.log B)^2/2))) := by
      rw [Real.exp_add,Real.rpow_def_of_pos hB0]
    _ ≤ Real.exp (Real.log B*(-A)) := Real.exp_le_exp.mpr he
    _ = _ := (Real.rpow_def_of_pos hB0 (-A)).symm

lemma constant_power_saving {c : ℝ} (hc : 0<c) (C p A : ℝ) : ∀ᶠ B : ℝ in atTop,
    C*B^p*Real.exp (-c*((Real.log B)^2/2)) ≤ (1/2)*B^(-A) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (2*C),
    power_exponential_saving hc (p+1) A] with B hB hC hs
  have hB0 : 0<B := by linarith
  have hcB : C≤B/2 := by linarith
  calc
    _ ≤ (B/2)*B^p*Real.exp (-c*((Real.log B)^2/2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcB (Real.rpow_nonneg hB0.le _)) (Real.exp_pos _).le
    _ = (1/2)*(B^(p+1)*Real.exp (-c*((Real.log B)^2/2))) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)

lemma half_floor_bound (S : ℝ) :
    (1/2:ℝ)^⌊S/2⌋₊ ≤ 2*Real.exp (-Real.log 2*(S/2)) := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hfloor := Nat.lt_floor_add_one (S/2)
  have hexponent : (⌊S/2⌋₊:ℝ)*(-Real.log 2) ≤ Real.log 2-Real.log 2*(S/2) := by
    nlinarith
  have hhalf : (1/2:ℝ)=Real.exp (-Real.log 2) := by
    rw [Real.exp_neg,Real.exp_log (by norm_num)]
    norm_num
  calc
    _ = Real.exp ((⌊S/2⌋₊:ℝ)*(-Real.log 2)) := by rw [Real.exp_nat_mul,← hhalf]
    _ ≤ Real.exp (Real.log 2-Real.log 2*(S/2)) := Real.exp_le_exp.mpr hexponent
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (by norm_num),neg_mul]

end ErdosPrimeInputs.LogSquaredDecay

end

end Erdos970

end OAI
