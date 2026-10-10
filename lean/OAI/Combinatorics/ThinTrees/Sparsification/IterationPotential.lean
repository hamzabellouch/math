import Mathlib
import OAI.Combinatorics.ThinTrees.Sparsification.HalfNumeric

namespace OAI

/-! Iteration potential. -/

section

noncomputable section
namespace AlgorithmicThinTrees.Iteration
open StrongThinTree

def lossB : ℝ := 80 / ((2:ℝ)^(1/16:ℝ)-1)
def potential (r : ℕ) : ℝ := Real.exp (lossB*(1-errorU r))

lemma lossB_pos : 0 < lossB := by
  unfold lossB
  exact div_pos (by norm_num) (sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num)))
lemma potential_pos (r : ℕ) : 0 < potential r := Real.exp_pos _
lemma potential_one_le {r : ℕ} (hr : 1 ≤ r) : 1 ≤ potential r := by
  exact Real.one_le_exp (mul_nonneg lossB_pos.le (sub_nonneg.mpr (errorU_le_one hr)))
lemma potential_le (r : ℕ) : potential r ≤ Real.exp lossB := by
  apply Real.exp_le_exp.mpr
  have := mul_nonneg lossB_pos.le (errorU_nonneg r)
  nlinarith

lemma potential_step {r s : ℕ} (hs : 0 < s) (hrs : (s:ℝ) ≤ (r:ℝ)/2) :
    (1+80*errorU r)*potential s ≤ potential r := by
  have hd : 0 < (2:ℝ)^(1/16:ℝ)-1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hm := mul_le_mul_of_nonneg_left (errorU_halving hs hrs) lossB_pos.le
  have hB : lossB*((2:ℝ)^(1/16:ℝ)-1)=80 := by
    unfold lossB
    exact div_mul_cancel₀ _ (ne_of_gt hd)
  have hdiff : 80*errorU r ≤ lossB*(errorU s-errorU r) := by
    have hBu := congrArg (fun x : ℝ => x*errorU r) hB
    nlinarith
  have he : 1+80*errorU r ≤ Real.exp (80*errorU r) := by
    simpa only [add_comm] using Real.add_one_le_exp (80*errorU r)
  calc
    _ ≤ Real.exp (80*errorU r)*potential s :=
      mul_le_mul_of_nonneg_right he (potential_pos s).le
    _ = Real.exp (80*errorU r+lossB*(1-errorU s)) := by
      rw [potential,Real.exp_add]
    _ ≤ potential r := by
      apply Real.exp_le_exp.mpr
      linarith

lemma coefficient_step {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hhalf : (s:ℝ) ≤ (r:ℝ)/2)
    (hratio : (1/2+3*GraphicHalf.halfError r)*(r:ℝ) ≤ (1+80*errorU r)*s) :
    potential s/(s:ℝ)*(1/2+3*GraphicHalf.halfError r) ≤ potential r/(r:ℝ) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hsR hrR).mpr
  have hp := potential_step hs hhalf
  have hm := mul_le_mul_of_nonneg_left hratio (potential_pos s).le
  have hp' := mul_le_mul_of_nonneg_right hp hsR.le
  nlinarith

end AlgorithmicThinTrees.Iteration
end

end

end OAI
