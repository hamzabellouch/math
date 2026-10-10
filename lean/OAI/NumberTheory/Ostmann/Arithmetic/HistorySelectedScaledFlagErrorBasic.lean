import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagErrorSum

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryUnnormalizedFlagError

lemma four_le_exp_two : (4:ℝ) ≤ Real.exp 2 := by
  have h : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hh := mul_le_mul h h (by norm_num : (0:ℝ) ≤ 2) (Real.exp_nonneg 1)
  have he : Real.exp 1*Real.exp 1 = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  nlinarith

theorem four_mul_prefactor_le (C m A : ℝ) (hm : 0 ≤ m) (hA : 0 ≤ A) :
    4*(A*Real.exp (C*(m+1))) ≤ A*Real.exp ((C+2)*(m+1)) := by
  have hh : (4:ℝ) ≤ Real.exp (2*(m+1)) := four_le_exp_two.trans
    (Real.exp_le_exp.mpr (by linarith))
  calc
    _ = A*(4*Real.exp (C*(m+1))) := by ring
    _ ≤ A*(Real.exp (2*(m+1))*Real.exp (C*(m+1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)) hA
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

lemma errorBudget_mono_prefactor {A B J D H atom mass : ℝ} {n : ℕ}
    (hAB : A ≤ B) (hJ : 0 ≤ J) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (ha : 0 ≤ atom) (hm : 0 ≤ mass) :
    errorBudget A J D H atom mass n ≤ errorBudget B J D H atom mass n := by
  unfold errorBudget
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAB hJ)
  positivity

end Ostmann.Arithmetic.HistoryUnnormalizedFlagError

end

end OAI
