import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! # Summable boundary budgets for slowly growing levels -/

noncomputable section
open scoped BigOperators
namespace DukePrimeDegree

lemma sum_exp_nat_le {C : ℝ} (hC : 0 ≤ C) (M : ℕ) :
    (∑ m ∈ Finset.range (M+1), Real.exp (C*(m:ℝ))) ≤
      (M+1:ℝ)*Real.exp (C*(M:ℝ)) := by
  calc
    _ ≤ ∑ _m ∈ Finset.range (M+1), Real.exp (C*(M:ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hC
      exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    _ = _ := by simp

lemma summable_linear_mul_exp {a : ℝ} (ha : a < 0) :
    Summable (fun k : ℕ => ((k:ℝ)+1)*Real.exp (a*(k:ℝ))) := by
  have hr : ‖Real.exp a‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr ha
  have h := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).add
    (summable_geometric_of_norm_lt_one hr)
  convert h using 1
  ext k
  rw [mul_comm a (k:ℝ),Real.exp_nat_mul]
  simp only [pow_one]
  ring

theorem summable_exponential_level_budget
    (L : ℕ → ℕ) {C δ K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hL : ∀ k, (L k:ℝ) ≤ δ*(k:ℝ)) (hdecay : C*δ < Real.log 2) :
    Summable (fun k : ℕ =>
      (∑ m ∈ Finset.range (L k+1), K*Real.exp (C*(m:ℝ)))*(1/2:ℝ)^k) := by
  have hsum := (summable_linear_mul_exp (sub_neg.mpr hdecay)).mul_left
    (K*max δ 1)
  apply Summable.of_nonneg_of_le (fun k =>
    mul_nonneg (Finset.sum_nonneg (fun m _ =>
      mul_nonneg hK (Real.exp_pos _).le)) (by positivity)) _ hsum
  intro k
  have hexp : Real.exp (C*(L k:ℝ)) ≤ Real.exp (C*δ*(k:ℝ)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ C*(δ*(k:ℝ)) := mul_le_mul_of_nonneg_left (hL k) hC
      _ = _ := by ring
  have hcount : (L k+1:ℝ) ≤ max δ 1*((k:ℝ)+1) := by
    have h₁ := mul_le_mul_of_nonneg_right (le_max_left δ 1) (Nat.cast_nonneg (α := ℝ) k)
    have h₂ := le_max_right δ 1
    nlinarith [hL k]
  have hbase : (1/2:ℝ)^k=Real.exp (-Real.log 2*(k:ℝ)) := by
    rw [mul_comm (-Real.log 2) (k:ℝ),Real.exp_nat_mul,
      Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
    simp only [one_div]
  calc
    _ ≤ (K*((L k+1:ℝ)*Real.exp (C*(L k:ℝ))))*(1/2:ℝ)^k := by
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sum_exp_nat_le hC (L k)) hK) (by positivity)
    _ ≤ (K*(max δ 1*((k:ℝ)+1)*Real.exp (C*δ*(k:ℝ))))*(1/2:ℝ)^k := by
      gcongr
    _ = _ := by
      rw [hbase]
      have he : Real.exp (C*δ*(k:ℝ))*Real.exp (-Real.log 2*(k:ℝ)) =
          Real.exp ((C*δ-Real.log 2)*(k:ℝ)) := by rw [←Real.exp_add]; congr 1; ring
      calc
        _ = K*max δ 1*((k:ℝ)+1)*
            (Real.exp (C*δ*(k:ℝ))*Real.exp (-Real.log 2*(k:ℝ))) := by ring
        _ = _ := by rw [he]; ring

end DukePrimeDegree

end

end OAI
