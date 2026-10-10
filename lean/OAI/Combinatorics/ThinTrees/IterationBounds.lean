import OAI.Combinatorics.ThinTrees.Restriction

namespace OAI

section

noncomputable section
namespace StrongThinTree

def iterationB : ℝ := 15 / ((2:ℝ)^(1/16:ℝ)-1)
def iterationPotential (r : ℕ) : ℝ := Real.exp (iterationB*(1-errorU r))

lemma iterationB_pos : 0 < iterationB := by
  unfold iterationB
  exact div_pos (by norm_num) (sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num)))
lemma errorU_nonneg (r : ℕ) : 0 ≤ errorU r := Real.rpow_nonneg (Nat.cast_nonneg _) _
lemma errorU_le_one {r : ℕ} (hr : 1 ≤ r) : errorU r ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hr) (by norm_num)
lemma iterationPotential_pos (r : ℕ) : 0 < iterationPotential r := Real.exp_pos _
lemma iterationPotential_one_le {r : ℕ} (hr : 1 ≤ r) : 1 ≤ iterationPotential r := by
  exact Real.one_le_exp (mul_nonneg iterationB_pos.le (sub_nonneg.mpr (errorU_le_one hr)))
lemma iterationPotential_le (r : ℕ) : iterationPotential r ≤ Real.exp iterationB := by
  apply Real.exp_le_exp.mpr
  have := mul_nonneg iterationB_pos.le (errorU_nonneg r)
  nlinarith

lemma errorU_halving {r s : ℕ} (hs : 0 < s) (hrs : (s:ℝ) ≤ (r:ℝ)/2) :
    (2:ℝ)^(1/16:ℝ)*errorU r ≤ errorU s := by
  have hsR : (0:ℝ) < s := Nat.cast_pos.mpr hs
  have hrR : (0:ℝ) < r := by linarith
  have hh := Real.rpow_le_rpow_of_nonpos hsR hrs (by norm_num : (-1/16:ℝ) ≤ 0)
  rw [Real.div_rpow hrR.le (by norm_num)] at hh
  have hi : (2:ℝ)^(-1/16:ℝ)=((2:ℝ)^(1/16:ℝ))⁻¹ := by
    rw [show (-1/16:ℝ)=-(1/16:ℝ) by ring,Real.rpow_neg (by norm_num)]
  simpa only [hi,div_inv_eq_mul,mul_comm,errorU] using hh

lemma iterationPotential_step {r s : ℕ} (hs : 0 < s) (hrs : (s:ℝ) ≤ (r:ℝ)/2) :
    (1+15*errorU r)*iterationPotential s ≤ iterationPotential r := by
  have hd : 0 < (2:ℝ)^(1/16:ℝ)-1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hm := mul_le_mul_of_nonneg_left (errorU_halving hs hrs) iterationB_pos.le
  have hB : iterationB*((2:ℝ)^(1/16:ℝ)-1)=15 := by
    unfold iterationB
    exact div_mul_cancel₀ _ (ne_of_gt hd)
  have hdiff : 15*errorU r ≤ iterationB*(errorU s-errorU r) := by
    have hBu := congrArg (fun x : ℝ => x*errorU r) hB
    nlinarith
  have he : 1+15*errorU r ≤ Real.exp (15*errorU r) := by
    simpa only [add_comm] using Real.add_one_le_exp (15*errorU r)
  calc
    _ ≤ Real.exp (15*errorU r)*iterationPotential s :=
      mul_le_mul_of_nonneg_right he (iterationPotential_pos s).le
    _ = Real.exp (15*errorU r+iterationB*(1-errorU s)) := by
      rw [iterationPotential,Real.exp_add]
    _ ≤ iterationPotential r := by
      apply Real.exp_le_exp.mpr
      linarith

lemma iteration_coefficient_step {r : ℕ} (h : StepNumeric r) :
    iterationPotential (stepCount r)/(stepCount r:ℝ)*(1/2+3*splitTau r) ≤
      iterationPotential r/(r:ℝ) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by have := h.rlarge; omega)
  have hsR : (0:ℝ) < stepCount r := lt_of_lt_of_le (by positivity) h.lower
  have hs : 0 < stepCount r := Nat.cast_pos.mp hsR
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hsR hrR).mpr
  have hp := iterationPotential_step hs h.upper
  have hm := mul_le_mul_of_nonneg_left h.ratio (iterationPotential_pos (stepCount r)).le
  have hp' := mul_le_mul_of_nonneg_right hp hsR.le
  nlinarith
end StrongThinTree

end
end

end OAI
