import OAI.NumberTheory.TotientAsymptotic.EnlargementCost
import Mathlib.Analysis.PSeries

namespace OAI

/-! The inverse-cube row contraction has a bounded full Jacobian. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def rowContractionError (h : ℕ) : ℝ := 1/(5*(h+1:ℝ)^3)

lemma rowContractionError_nonneg (h : ℕ) : 0 ≤ rowContractionError h := by
  unfold rowContractionError
  positivity

lemma rowContractionError_weighted_summable :
    Summable (fun h : ℕ => (h:ℝ)*rowContractionError h) := by
  have hs : Summable (fun h : ℕ => (1/5:ℝ)*(1/((h+1:ℕ):ℝ)^2)) :=
    ((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))).mul_left _
  apply Summable.of_nonneg_of_le
    (fun h => mul_nonneg (Nat.cast_nonneg h) (rowContractionError_nonneg h)) _ hs
  intro h
  have hp : (0:ℝ) < h+1 := by positivity
  calc
    _ ≤ (h+1:ℝ)*rowContractionError h :=
      mul_le_mul_of_nonneg_right (by linarith) (rowContractionError_nonneg h)
    _ = _ := by
      unfold rowContractionError
      push_cast
      field_simp [hp.ne']

def rowContractionCost : ℝ := ∑' h : ℕ,(h:ℝ)*rowContractionError h

lemma rowContractionCost_nonneg : 0 ≤ rowContractionCost :=
  tsum_nonneg (fun h => mul_nonneg (Nat.cast_nonneg h) (rowContractionError_nonneg h))

lemma row_contraction_jacobian {m N : ℕ} (hNm : N ≤ m) :
    (∏ i : Fin N,enlargementScale (fun r => 1+rowContractionError (m-r)) i) ≤
      Real.exp rowContractionCost := by
  apply (enlargement_jacobian_bound
    (fun r => by linarith [rowContractionError_nonneg (m-r)])).trans
  apply Real.exp_le_exp.mpr
  simp only [add_sub_cancel_left]
  have hs : (∑ r ∈ Finset.range N,((N-r:ℕ):ℝ)*rowContractionError (m-r)) ≤
      ∑ r ∈ Finset.range m,((m-r:ℕ):ℝ)*rowContractionError (m-r) := by
    apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNm)
      (fun r _ _ => mul_nonneg (Nat.cast_nonneg _) (rowContractionError_nonneg _)))
    apply Finset.sum_le_sum
    intro r _
    apply mul_le_mul_of_nonneg_right _ (rowContractionError_nonneg _)
    exact_mod_cast Nat.sub_le_sub_right hNm r
  apply hs.trans
  simpa only [Nat.sub_zero,Nat.zero_add,rowContractionCost] using
    reverse_perturbation_sum_le (P:=0) (Nat.zero_le m) rowContractionError
      rowContractionError_nonneg rowContractionError_weighted_summable

lemma row_contraction_coordinate {m N : ℕ} (hNm : N ≤ m) (i : Fin N) :
    enlargementScale (fun r => 1+rowContractionError (m-r)) i ≤
      Real.exp rowContractionCost := by
  have hi : i.val < m := i.isLt.trans_le hNm
  simpa only [Nat.sub_zero,Nat.zero_add,rowContractionCost] using
    reverse_enlargement_coordinate (H:=0) (Nat.zero_le m) rowContractionError
      rowContractionError_nonneg rowContractionError_weighted_summable i hi

lemma inverse_cube_row_factor {h : ℕ} (hh : 1 ≤ h) :
    (1+1/(5*(h:ℝ)^3))⁻¹ ≤ 1-1/(10*(h:ℝ)^3) := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hp : (0:ℝ) < (h:ℝ)^3 := by positivity
  have hc : 1 ≤ (h:ℝ)^3 := one_le_pow₀ hh'
  have he : 0 ≤ 1/(10*(h:ℝ)^3) := by positivity
  have he1 : 1/(10*(h:ℝ)^3) ≤ 1/10 := by
    apply (div_le_iff₀ (by positivity : 0 < 10*(h:ℝ)^3)).mpr
    nlinarith only [hc]
  have hb : 0 < 1+1/(5*(h:ℝ)^3) := by positivity
  rw [←one_div (1+1/(5*(h:ℝ)^3))]
  apply (div_le_iff₀ hb).mpr
  have hident : 1/(5*(h:ℝ)^3)=2*(1/(10*(h:ℝ)^3)) := by ring
  rw [hident]
  nlinarith only [he,he1]

end TotientAsymptotic

end

end OAI
