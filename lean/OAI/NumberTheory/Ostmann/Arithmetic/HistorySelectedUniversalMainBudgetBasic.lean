import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsNormalize
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceXi
import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedUniversalMainBudget
open Construction Conclusion HistoryProductWindows Filter

def fixedCost (k : ℕ) : ℝ :=
  ∑l∈Finset.range (k+1),
    |Real.log 64+((nominalInheritedWidth k l+2)+nominalRemovedWidth k l)+
      sourceXiConstant l k (2+2*(k:ℝ))|

theorem fixedCost_nonneg (k : ℕ) : 0 ≤ fixedCost k :=
  Finset.sum_nonneg (fun _ _=>abs_nonneg _)

theorem fixedCost_bounds (k l : ℕ) (hl : l ≤ k) :
    Real.log 64+((nominalInheritedWidth k l+2)+nominalRemovedWidth k l)+
      sourceXiConstant l k (2+2*(k:ℝ)) ≤ fixedCost k := by
  unfold fixedCost
  apply (le_abs_self _).trans
  exact Finset.single_le_sum
    (f := fun j : ℕ=>|Real.log 64+((nominalInheritedWidth k j+2)+nominalRemovedWidth k j)+
      sourceXiConstant j k (2+2*(k:ℝ))|)
    (fun _ _=>abs_nonneg _) (Finset.mem_range.mpr (show l<k+1 by omega))

theorem fixed_cost_eventually {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀l ≤ k,
      Real.log 64+((nominalInheritedWidth k l+2)+nominalRemovedWidth k l)+
        sourceXiConstant l k (2+2*(k:ℝ)) ≤ (bulkSize k L:ℝ) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop (fixedCost k)] with L hL
  exact fun l hl=>(fixedCost_bounds k l hl).trans hL

theorem scalar_main_product_le {m Δ W Xi : ℝ} {r b : ℕ}
    (hm : 0 ≤ m) (hr : 1 ≤ r) (hb : (2*b:ℕ) ≤ m)
    (hfixed : Real.log 64+W+Xi ≤ m) :
    64*(Real.exp W*Real.exp (-((r:ℕ):ℝ)*Δ+Xi))*
      (2:ℝ)^(r*(2*b))*(3:ℝ)^(r*(2*b))*
      Real.exp (2*(r:ℝ)*m)*Real.exp (2*(r:ℝ)*Δ+m) ≤ 
        Real.exp ((r:ℝ)*(Δ+16*m)) := by
  have hlog₂ : Real.log 2 ≤ (1:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hlog₃ : Real.log 3 ≤ (2:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num at h
    exact h
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hrm : m ≤ (r:ℝ)*m := le_mul_of_one_le_left hm hrR
  have hn : ((r*(2*b):ℕ):ℝ) ≤ (r:ℝ)*m := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
  have hn0 : (0:ℝ) ≤ (r*(2*b):ℕ) := Nat.cast_nonneg _
  have he₂ : ((r*(2*b):ℕ):ℝ)*Real.log 2 ≤ (r:ℝ)*m :=
    (by nlinarith : ((r*(2*b):ℕ):ℝ)*Real.log 2 ≤ ((r*(2*b):ℕ):ℝ)).trans hn
  have he₃ : ((r*(2*b):ℕ):ℝ)*Real.log 3 ≤ 2*(r:ℝ)*m := by
    nlinarith
  have h64 : (64:ℝ)=Real.exp (Real.log 64) := (Real.exp_log (by norm_num)).symm
  have h₂ : (2:ℝ)^(r*(2*b))=Real.exp (((r*(2*b):ℕ):ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have h₃ : (3:ℝ)^(r*(2*b))=Real.exp (((r*(2*b):ℕ):ℝ)*Real.log 3) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<3)]
  rw [h64,h₂,h₃]
  simp only [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

end Ostmann.Arithmetic.HistorySelectedUniversalMainBudget

end

end OAI
