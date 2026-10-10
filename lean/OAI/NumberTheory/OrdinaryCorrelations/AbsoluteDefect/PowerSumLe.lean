import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter

namespace OrdinaryPowerBounds

lemma power_sum_le {δ : ℝ} (hδ : 0<δ) :
    (∑' n : ℕ, (n:ℝ)^(-(1+δ))) ≤ 1+1/δ := by
  have hs : Summable (fun n : ℕ => (n:ℝ)^(-(1+δ))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hi := AntitoneOn.tsum_comp_add_le_integral (f:=fun x : ℝ => x^(-(1+δ))) 1
    (by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by simp only [Nat.cast_one,Set.mem_Ici] at hx; linarith)
        hxy (by linarith))
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(1+δ)< -1) (by norm_num))
    (fun x hx => Real.rpow_nonneg (by simp only [Nat.cast_one,Set.mem_Ioi] at hx; linarith) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -(1+δ)< -1) (by norm_num : (0:ℝ)<(1:ℕ))] at hi
  have hz : (0:ℝ)^(-(1+δ))=0 := Real.zero_rpow (by linarith)
  have he := hs.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    Nat.cast_one,Real.one_rpow,hz] at he
  have ht : ∑' n : ℕ, ((n+2:ℕ):ℝ)^(-(1+δ)) ≤ 1/δ := by
    simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.cast_one,Real.one_rpow,
      show -(1+δ)+1 = -δ by ring,div_neg,neg_div,neg_neg] using hi
  linarith

lemma LSeries_norm_le_power {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1<s.re) :
    ‖LSeries f s‖ ≤ ∑' n : ℕ, (n:ℝ)^(-s.re) := by
  have hsum := LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) hs
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  apply hsum.norm.tsum_le_tsum _ (Real.summable_nat_rpow.mpr (by linarith))
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n=0
  · simp [hn,Real.zero_rpow (by linarith : -s.re≠0)]
  · rw [ite_eq_right hn,Real.rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]
    exact div_le_div_of_nonneg_right (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem LSeries_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1<s.re) : ‖LSeries f s‖ ≤ 1+1/(s.re-1) := by
  apply (LSeries_norm_le_power hf hs).trans
  simpa only [show 1+(s.re-1)=s.re by ring] using
    power_sum_le (by linarith : 0<s.re-1)

end OrdinaryPowerBounds

end

end OAI
