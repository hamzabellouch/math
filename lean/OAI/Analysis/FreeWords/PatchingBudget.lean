import Mathlib

namespace OAI

noncomputable section

namespace KKLocalPatching

noncomputable section

def patchingBudget (δ C t : ℝ) : ℝ := δ*(Real.exp (C*t)-1)

theorem continuous_patchingBudget (δ C : ℝ) : Continuous (patchingBudget δ C) := by
  unfold patchingBudget
  fun_prop

@[simp] theorem patchingBudget_zero (δ C : ℝ) : patchingBudget δ C 0=0 := by
  simp [patchingBudget]

theorem patchingBudget_nonneg {δ C t : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C) (ht : 0 ≤ t) :
    0 ≤ patchingBudget δ C t := by
  exact mul_nonneg hδ (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hC ht)))

theorem patchingBudget_increment {δ C D η t s : ℝ}
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hη : 0 < η) (hC : 0 ≤ C)
    (hdom : D*(2/η+1) ≤ C) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    patchingBudget δ C t+D*(2*patchingBudget δ C t/η+δ)*s  ≤  patchingBudget δ C (t+s) := by
  let E := Real.exp (C*t)
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg hC ht)
  have hE0 : 0 ≤ E := (zero_le_one.trans hE)
  have hB : patchingBudget δ C t ≤ δ*E := by
    dsimp only [patchingBudget,E]
    nlinarith
  have hδE : δ ≤ δ*E := by nlinarith
  have hcoeff : D*(2*patchingBudget δ C t/η+δ) ≤ δ*E*C := by
    calc
      _  ≤  D*(2*(δ*E)/η+δ*E) := mul_le_mul_of_nonneg_left
        (add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by norm_num)) hη.le) hδE) hD
      _ = (δ*E)*(D*(2/η+1)) := by ring
      _  ≤  δ*E*C := mul_le_mul_of_nonneg_left hdom (mul_nonneg hδ hE0)
  have hex : C*s+1 ≤ Real.exp (C*s) := Real.add_one_le_exp (C*s)
  have hstep : patchingBudget δ C t+(δ*E*C)*s ≤ patchingBudget δ C (t+s) := by
    have h := mul_le_mul_of_nonneg_left hex (mul_nonneg hδ hE0)
    dsimp only [patchingBudget]
    rw [mul_add,Real.exp_add]
    change δ*(E-1)+δ*E*C*s ≤ δ*(E*Real.exp (C*s)-1)
    nlinarith
  exact (add_le_add (le_refl (patchingBudget δ C t)) (mul_le_mul_of_nonneg_right hcoeff hs)).trans hstep

end

end KKLocalPatching
end

end OAI
