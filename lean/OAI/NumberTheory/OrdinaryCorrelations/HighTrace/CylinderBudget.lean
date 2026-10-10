import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RepeatedCenterUnlitCount

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical Filter

noncomputable def cylinderBudget (m : ℕ) : ℝ := (2^m*max 1 (m^(m+1)):ℕ)

lemma coefficient_le_cylinderBudget (m : ℕ) :
    (max 1 (m^(m+1)):ℕ) ≤ cylinderBudget m := by
  unfold cylinderBudget
  exact_mod_cast Nat.le_mul_of_pos_left _ (by positivity : 0 < 2^m)

lemma cylinderBudget_nonneg (m : ℕ) : 0 ≤ cylinderBudget m := Nat.cast_nonneg _

lemma cylinderBudget_le_exp (m : ℕ) (B : ℝ) (hB : 2 ≤ B) (hm : (m:ℝ) ≤ B^2) :
    cylinderBudget m ≤ Real.exp (5*(m:ℝ)*Real.log B) := by
  have hB0 : 0 < B := by linarith
  by_cases hz : m=0
  · subst m
    simp [cylinderBudget]
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hz
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hp : 1 ≤ m^(m+1) := Nat.one_le_pow _ _ hm1
  have hlog : Real.log (m:ℝ) ≤ 2*Real.log B := by
    calc
      _ ≤ Real.log (B^2) := Real.log_le_log hmpos hm
      _ = _ := by simp only [Real.log_pow,Nat.cast_ofNat]
  have hlog0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have htwo : (2:ℝ)^m ≤ Real.exp ((m:ℝ)*Real.log B) := by
    calc
      _ ≤ B^m := pow_le_pow_left₀ (by norm_num) hB m
      _ = _ := by rw [← Real.rpow_natCast,Real.rpow_def_of_pos hB0]; ring_nf
  have hpow : (m:ℝ)^(m+1) ≤ Real.exp (4*(m:ℝ)*Real.log B) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos hmpos]
    apply Real.exp_le_exp.mpr
    have hc : ((m+1:ℕ):ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast (show m+1 ≤ 2*m by omega)
    calc
      Real.log (m:ℝ)*((m+1:ℕ):ℝ) ≤ (2*Real.log B)*((m+1:ℕ):ℝ) :=
        mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _)
      _ ≤ (2*Real.log B)*(2*(m:ℝ)) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  unfold cylinderBudget
  rw [max_eq_right hp]
  push_cast
  calc
    _ ≤ Real.exp ((m:ℝ)*Real.log B)*Real.exp (4*(m:ℝ)*Real.log B) :=
      mul_le_mul htwo hpow (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma source_cylinder_budget (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, cylinderBudget (sourceListSlotBudget C₀ B) ≤
      Real.exp (5*(sourceListSlotBudget C₀ B:ℝ)*Real.log B) := by
  filter_upwards [source_list_slots_power C₀ hC₀,
    eventually_const_mul_rpow_le (1-rho+4*epsilon+rho/8) 2 4 (by norm_num [rho,epsilon]),
    eventually_ge_atTop (2:ℝ)] with B hM hpow hB
  apply cylinderBudget_le_exp _ B hB
  exact (hM.trans hpow).trans_eq (by rw [Real.rpow_two])

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
