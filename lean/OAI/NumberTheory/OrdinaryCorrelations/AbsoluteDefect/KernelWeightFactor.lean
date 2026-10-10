import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.KernelConstant

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryCorrelations.Completion
open Finset ArithmeticFunction

lemma kernelWeight_factor {f : ℕ → ℂ} (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖kernel f n‖ / (n:ℝ) = kernelWeight f σ n * (n:ℝ)^(σ-1) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [kernelWeight,mul_assoc,←Real.rpow_add hn0]
  have he : -σ + (σ-1) = (-1:ℝ) := by ring
  rw [he,Real.rpow_neg_one,div_eq_mul_inv]

theorem kernelTail_le {f : ℕ → ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    (h1 : f 1 = 1) {σ Y : ℝ} (hσ : 1/2 < σ) (hσ1 : σ ≤ 1) (hY : 0 < Y)
    (S : Finset ℕ) :
    (∑ n ∈ S.filter (fun (n : ℕ) => Y < (n:ℝ)), ‖kernel f n‖ / (n:ℝ)) ≤
      Y^(σ-1) * kernelConstant σ := by
  classical
  calc
    (∑ n ∈ S.filter (fun (n : ℕ) => Y < (n:ℝ)), ‖kernel f n‖ / (n:ℝ)) ≤
        ∑ n ∈ S.filter (fun (n : ℕ) => Y < (n:ℝ)), kernelWeight f σ n * Y^(σ-1) := by
      apply sum_le_sum
      intro n hn
      have hYn := (mem_filter.mp hn).2
      have hn0 : 0 < n := by exact_mod_cast hY.trans hYn
      rw [kernelWeight_factor σ hn0]
      apply mul_le_mul_of_nonneg_left _ (kernelWeight_nonneg _ _ _)
      exact Real.rpow_le_rpow_of_nonpos hY hYn.le (by linarith)
    _ = (∑ n ∈ S.filter (fun (n : ℕ) => Y < (n:ℝ)), kernelWeight f σ n) * Y^(σ-1) :=
      (sum_mul _ _ _).symm
    _ ≤ kernelConstant σ * Y^(σ-1) := mul_le_mul_of_nonneg_right
      (kernelWeight_sum_le hf hm h1 hσ _) (Real.rpow_nonneg hY.le _)
    _ = Y^(σ-1) * kernelConstant σ := mul_comm _ _

theorem kernelTail_quarter {f : ℕ → ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    (h1 : f 1 = 1) {Y : ℝ} (hY : 0 < Y) (S : Finset ℕ) :
    (∑ n ∈ S.filter (fun (n : ℕ) => Y < (n:ℝ)), ‖kernel f n‖ / (n:ℝ)) ≤
      Y^(-(1/4:ℝ)) * kernelConstant (3/4) := by
  have he : (3:ℝ)/4-1 = -(1/4:ℝ) := by norm_num
  simpa only [he] using kernelTail_le hf hm h1 (by norm_num : (1:ℝ)/2 < 3/4)
    (by norm_num : (3:ℝ)/4 ≤ 1) hY S

end OrdinaryCorrelations.Completion

end

end OAI
