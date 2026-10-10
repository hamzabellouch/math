import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGap
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationDataNorm

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedCancellation

def compiledConstant (C : ℝ) (n : ℕ) : ℝ := ((n:ℝ)+1)*C+10

theorem compiledConstant_nonneg {C : ℝ} (hC : 0≤C) (n : ℕ) :
    0≤compiledConstant C n := by unfold compiledConstant; positivity

theorem compiledCost_bounds (C z L : ℝ) (d n : ℕ) (hC : 0≤C) :
    0≤historyPolynomialCost C z d L ∧
    historyPolynomialCost C z d L≤historyPolynomialCost (compiledConstant C n) z d L ∧
    (n:ℝ)*historyPolynomialCost C z d L≤historyPolynomialCost (compiledConstant C n) z d L ∧
    historyPolynomialCost C z d L+7≤historyPolynomialCost (compiledConstant C n) z d L := by
  have hbase : 1≤(1+(⌊z*L⌋₊:ℝ))^d := one_le_pow₀ (by have hh : (0:ℝ)≤(⌊z*L⌋₊:ℝ) := Nat.cast_nonneg _; linarith)
  have hP : 0≤C*(1+(⌊z*L⌋₊:ℝ))^d := mul_nonneg hC (by positivity)
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg _
  unfold historyPolynomialCost compiledConstant
  constructor
  · exact hP
  constructor
  · nlinarith [mul_nonneg hn hP]
  constructor
  · nlinarith
  · nlinarith [mul_nonneg hn hP]

theorem compiledCost_seven_exp (C z L : ℝ) (d n : ℕ) (hC : 0≤C) :
    7*Real.exp (historyPolynomialCost C z d L) ≤
      Real.exp (historyPolynomialCost (compiledConstant C n) z d L) := by
  have hlog : Real.log 7≤7 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<7)
    linarith
  have hb := (compiledCost_bounds C z L d n hC).2.2.2
  calc
    _ = Real.exp (historyPolynomialCost C z d L+Real.log 7) := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<7)]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem crossLogWidth_eq {τ : Type*} [Fintype τ] (A B : τ → ℝ) :
    3+(∑i : Unit ⊕ (τ ⊕ τ),
      (Sum.elim (fun _ : Unit => (0:ℝ)) (Sum.elim B B) i -
        Sum.elim (fun _ : Unit => -Real.log 2) (Sum.elim A A) i)) =
      3+Real.log 2+2*(∑i : τ,(B i-A i)) := by
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,
    sub_neg_eq_add,zero_add]
  ring

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
