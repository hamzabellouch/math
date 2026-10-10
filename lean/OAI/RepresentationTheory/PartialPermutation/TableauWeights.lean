import Mathlib
import OAI.RepresentationTheory.PartialPermutation.TailBounds
import OAI.RepresentationTheory.PartialPermutation.DeficitCounts
import OAI.RepresentationTheory.PartialPermutation.PartitionAsymptotics

namespace OAI

section
namespace PartialPermutation
namespace TableauZeta
noncomputable section
open Finset Filter
open Tableau DiagramCounting

lemma inverse_tableau_bound (μ : YoungDiagram) (u : ℝ) (hu : 0 < u) :
    (standardCount μ : ℝ)^(-u) ≤
      Real.exp (u*Real.log 2 - (u*Real.log 2/8)*(deficit μ : ℝ)) := by
  have hc : (0:ℝ)<standardCount μ := by exact_mod_cast standardCount_pos μ
  have hb : (2:ℝ)^(deficit μ/8) ≤ standardCount μ := by
    exact_mod_cast tail_power_lower_bound μ
  have hh := Real.rpow_le_rpow_of_nonpos (show (0:ℝ)<2^(deficit μ/8) by positivity)
    hb (neg_nonpos.mpr hu.le)
  apply hh.trans
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hk : (deficit μ : ℝ) < 8*(deficit μ/8 : ℕ)+8 := by
    exact_mod_cast (show deficit μ < 8*(deficit μ/8)+8 by omega)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hk.le (show 0 ≤ u*Real.log 2/8 by positivity)
  nlinarith

def majorant (u : ℝ) (k : ℕ) : ℝ :=
  2*(partitionCount k : ℝ)*Real.exp (u*Real.log 2 - (u*Real.log 2/8)*k)

lemma summable_majorant (u : ℝ) (hu : 0 < u) : Summable (majorant u) := by
  let a := u*Real.log 2/8
  have ha : 0 < a := by dsimp [a]; exact div_pos (mul_pos hu (Real.log_pos (by norm_num))) (by norm_num)
  have hs : Summable (fun k : ℕ => (2*Real.exp (u*Real.log 2))*Real.exp ((k:ℝ)*(-a/2))) :=
    (Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_left _
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [partitionCount_subexponential (a/2) (by positivity)] with k hk
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ majorant u k by unfold majorant; positivity)]
  calc
    majorant u k ≤ 2*Real.exp ((a/2)*k)*Real.exp (u*Real.log 2-a*k) := by
      unfold majorant
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) (Real.exp_nonneg _)
    _ = (2*Real.exp (u*Real.log 2))*Real.exp ((k:ℝ)*(-a/2)) := by
      rw [mul_assoc,← Real.exp_add,mul_assoc,← Real.exp_add]
      congr 2
      ring

def inverseWeight (u : ℝ) (μ : YoungDiagram) : ℝ :=
  if deficit μ=0 then 0 else (standardCount μ:ℝ)^(-u)

def deficitTerm (n : ℕ) (u : ℝ) (k : ℕ) : ℝ :=
  ∑ μ : ShapeDeficit n k, inverseWeight u μ.1.1

def nontrivialSum (n : ℕ) (u : ℝ) : ℝ :=
  ∑ μ : Shape n, inverseWeight u μ.1

def fullSum (n : ℕ) (u : ℝ) : ℝ :=
  ∑ μ : Shape n, (standardCount μ.1:ℝ)^(-u)

lemma inverseWeight_nonneg (u : ℝ) (μ : YoungDiagram) : 0 ≤ inverseWeight u μ := by
  unfold inverseWeight
  split_ifs <;> positivity

lemma deficitTerm_nonneg (n : ℕ) (u : ℝ) (k : ℕ) : 0 ≤ deficitTerm n u k :=
  Finset.sum_nonneg (fun μ _ => inverseWeight_nonneg u μ.1.1)

lemma deficitTerm_bound (n : ℕ) (u : ℝ) (hu : 0 < u) (k : ℕ) :
    ‖deficitTerm n u k‖ ≤ majorant u k := by
  rw [Real.norm_eq_abs,abs_of_nonneg (deficitTerm_nonneg n u k)]
  have hcard : (Fintype.card (ShapeDeficit n k):ℝ) ≤ 2*partitionCount k := by
    exact_mod_cast deficit_count_le n k
  calc
    deficitTerm n u k ≤ ∑ μ : ShapeDeficit n k,
        Real.exp (u*Real.log 2 - (u*Real.log 2/8)*k) := by
      apply Finset.sum_le_sum
      intro μ _
      unfold inverseWeight
      split_ifs
      · exact Real.exp_nonneg _
      · have hh := inverse_tableau_bound μ.1.1 u hu
        have he : deficit μ.1.1=k := μ.2
        simpa only [he] using hh
    _ = (Fintype.card (ShapeDeficit n k):ℝ)*
        Real.exp (u*Real.log 2 - (u*Real.log 2/8)*k) := by simp
    _ ≤ majorant u k := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)

end
end TableauZeta
end PartialPermutation
end

end OAI
