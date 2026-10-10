import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion

def stepGapCoefficient (BD Bz : ℝ) (k j : ℕ) : ℝ :=
  (2 : ℝ)^j * (BD + Bz * Real.log (bulkScale k) + (2/5 : ℝ) * Real.log ((2 : ℝ)^j))

def scaleLinearConstant (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  1 + |Bs + 8 * Real.log (bulkScale k)| +
    ∑ j ∈ Finset.range k, |stepGapCoefficient BD Bz k j| + (2 : ℝ)^k

theorem scaleLinearConstant_pos (Bs BD Bz : ℝ) (k : ℕ) :
    0 < scaleLinearConstant Bs BD Bz k := by
  unfold scaleLinearConstant
  positivity

theorem stepGap_le_linear (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) {j : ℕ} (hj : j < k) :
    stepGap BD Bz k L j ≤ scaleLinearConstant Bs BD Bz k * (bulkSize k L : ℝ) := by
  have hj' : |stepGapCoefficient BD Bz k j| ≤
      ∑ i ∈ Finset.range k, |stepGapCoefficient BD Bz k i| :=
    Finset.single_le_sum (f := fun i => |stepGapCoefficient BD Bz k i|)
      (fun i hi => abs_nonneg _) (Finset.mem_range.mpr hj)
  have hc : stepGapCoefficient BD Bz k j ≤ scaleLinearConstant Bs BD Bz k := by
    have := le_abs_self (stepGapCoefficient BD Bz k j)
    have h₁ := abs_nonneg (Bs + 8 * Real.log (bulkScale k))
    have h₂ : 0 ≤ (2 : ℝ)^k := by positivity
    unfold scaleLinearConstant
    linarith
  exact mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)

theorem frequencyBudget_le_linear (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    frequencyBudget Bs BD Bz k L l ≤ scaleLinearConstant Bs BD Bz k * (bulkSize k L : ℝ) := by
  have hm' : (1 : ℝ) ≤ bulkSize k L := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ bulkSize k L := Nat.cast_nonneg _
  have hsqrt : Real.sqrt (bulkSize k L) ≤ (bulkSize k L : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hm0,by nlinarith⟩
  have hpow : (2 : ℝ)^l ≤ (2 : ℝ)^k := pow_le_pow_right₀ (by norm_num) hl
  have hsum : (∑ j ∈ Finset.range l, stepGapCoefficient BD Bz k j) ≤
      ∑ j ∈ Finset.range k, |stepGapCoefficient BD Bz k j| := by
    apply (Finset.sum_le_sum (fun j hj => le_abs_self _)).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hl) (fun _ _ _ => abs_nonneg _)
  have hfirst := mul_le_mul_of_nonneg_right (le_abs_self (Bs + 8 * Real.log (bulkScale k))) hm0
  have hmiddle := mul_le_mul_of_nonneg_right hsum hm0
  have hlast := mul_le_mul hpow hsqrt (Real.sqrt_nonneg _) (by positivity)
  have hid : ∑ j ∈ Finset.range l, stepGap BD Bz k L j =
      (∑ j ∈ Finset.range l, stepGapCoefficient BD Bz k j) * (bulkSize k L : ℝ) := by
    simp only [stepGap,stepGapCoefficient,Finset.sum_mul]
  unfold frequencyBudget initialGap
  rw [hid]
  unfold scaleLinearConstant
  nlinarith

theorem log_frequencyBound_add_one_le_linear (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    Real.log ((frequencyBound Bs BD Bz k L l : ℝ) + 1) ≤
      (scaleLinearConstant Bs BD Bz k + 1) * (bulkSize k L : ℝ) := by
  let C := scaleLinearConstant Bs BD Bz k
  let m : ℝ := bulkSize k L
  have hm' : 1 ≤ m := by dsimp [m]; exact_mod_cast hm
  have hCm : 0 ≤ C * m := mul_nonneg (scaleLinearConstant_pos Bs BD Bz k).le (by positivity)
  have hfloor : (frequencyBound Bs BD Bz k L l : ℝ) ≤ Real.exp (C * m) :=
    (Nat.floor_le (Real.exp_pos _).le).trans
      (Real.exp_le_exp.mpr (frequencyBudget_le_linear Bs BD Bz k L hm hl))
  have hone : 1 ≤ Real.exp (C * m) := Real.one_le_exp hCm
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  calc
    _ ≤ Real.log (2 * Real.exp (C * m)) := Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 2 + C * m := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
    _ ≤ (C + 1) * m := by nlinarith

end Ostmann.Conclusion

end

end OAI
