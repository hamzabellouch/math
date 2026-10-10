import Mathlib
import OAI.Probability.SKBarriers.Model

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def siteChoice {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) : ℝ :=
  Real.exp (β*spin b*localField J x i)/(2*Real.cosh (β*localField J x i))

theorem siteChoice_pos {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) :
    0 < siteChoice β J x i b := by
  apply div_pos (Real.exp_pos _)
  exact mul_pos (by norm_num) (Real.cosh_pos _)

theorem siteChoice_sum {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) (i : Fin n) :
    ∑ b : Bool, siteChoice β J x i b = 1 := by
  simp only [siteChoice,Fintype.sum_bool,spin,Bool.false_eq_true,ite_false,ite_true,mul_one,
    mul_neg_one,neg_mul]
  rw [← add_div,Real.cosh_eq]
  have H : Real.exp (β*localField J x i)+Real.exp (-(β*localField J x i)) ≠ 0 := by positivity
  field_simp

theorem siteChoice_fiber {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) (i : Fin n) :
    (∑ b : Bool, if Function.update x i b = y then siteChoice β J x i b else 0) =
      if Function.update x i (y i) = y then siteChoice β J x i (y i) else 0 := by
  classical
  apply Finset.sum_eq_single (y i)
  · intro b _ hbi
    have H : Function.update x i b ≠ y := by
      intro he
      have he' := congrFun he i
      exact hbi (by simpa only [Function.update_self] using he')
    simp only [ite_eq_right H]
  · simp

theorem heatBath_eq_siteChoice {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) :
    heatBath β J x y = (∑ i : Fin n, ∑ b : Bool,
      if Function.update x i b = y then siteChoice β J x i b else 0)/(n:ℝ) := by
  unfold heatBath
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [siteChoice_fiber]
  rfl

theorem heatBath_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) :
    0 ≤ heatBath β J x y := by
  rw [heatBath_eq_siteChoice]
  apply div_nonneg _ (Nat.cast_nonneg n)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact (siteChoice_pos β J x i b).le
  · rfl

theorem heatBath_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (x : Config n) :
    ∑ y : Config n, heatBath β J x y = 1 := by
  classical
  simp only [heatBath_eq_siteChoice]
  rw [← Finset.sum_div,Finset.sum_comm]
  have HS : (∑ i : Fin n, ∑ y : Config n, ∑ b : Bool,
      if Function.update x i b = y then siteChoice β J x i b else 0) = (n:ℝ) := by
    calc
      _ = ∑ i : Fin n, ∑ b : Bool, siteChoice β J x i b := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp
      _ = _ := by simp only [siteChoice_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,mul_one]
  rw [HS]
  exact div_self (by exact_mod_cast hn.ne')

theorem discreteKernel_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (k : ℕ) (x y : Config n) :
    0 ≤ discreteKernel β J k x y := by
  induction k generalizing x y with
  | zero => simp only [discreteKernel]; split_ifs <;> norm_num
  | succ k ih =>
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (heatBath_nonneg β J x z) (ih z y))

theorem discreteKernel_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (k : ℕ) (x : Config n) :
    ∑ y : Config n, discreteKernel β J k x y = 1 := by
  classical
  induction k generalizing x with
  | zero => simp [discreteKernel]
  | succ k ih =>
    simp only [discreteKernel]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,ih,mul_one]
    exact heatBath_sum hn β J x

theorem discreteKernel_le_one {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (k : ℕ) (x y : Config n) : discreteKernel β J k x y ≤ 1 := by
  rw [← discreteKernel_sum hn β J k x]
  exact Finset.single_le_sum (fun z _ => discreteKernel_nonneg β J k x z) (Finset.mem_univ y)

end SK.Analytic

end
end

end

end OAI
