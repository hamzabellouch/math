import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators

lemma bulkScale_one_le {k : ℕ} (hk : 1 ≤ k) : 1 ≤ bulkScale k := by
  unfold bulkScale
  exact one_le_pow₀ (by exact_mod_cast hk)

theorem frequencyBudget_nonneg {Bs BD Bz : ℝ} (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    {k : ℕ} (hk : 1 ≤ k) (L : ℝ) (l : ℕ) : 0 ≤ frequencyBudget Bs BD Bz k L l := by
  have hlog := Real.log_nonneg (bulkScale_one_le hk)
  have hgap : 0 ≤ initialGap Bs k L := by unfold initialGap; positivity
  have hstep (j : ℕ) : 0 ≤ stepGap BD Bz k L j := by
    have hlogj := Real.log_nonneg (show (1:ℝ) ≤ (2:ℝ)^j from one_le_pow₀ (by norm_num))
    unfold stepGap
    positivity
  unfold frequencyBudget
  exact add_nonneg (add_nonneg hgap (Finset.sum_nonneg fun j _=>hstep j)) (by positivity)

theorem frequency_card_le_exp {Bs BD Bz : ℝ} (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    {k : ℕ} (hk : 1 ≤ k) (L : ℝ) (l : ℕ) :
    2*(frequencyBound Bs BD Bz k L l:ℝ)+1 ≤ 3*Real.exp (frequencyBudget Bs BD Bz k L l) := by
  have he := Real.one_le_exp (frequencyBudget_nonneg hBs hBD hBz hk L l)
  have hf := Nat.floor_le (Real.exp_pos (frequencyBudget Bs BD Bz k L l)).le
  change (frequencyBound Bs BD Bz k L l:ℝ) ≤ _ at hf
  linarith

theorem final_bad_exponent_le {Bs BD Bz : ℝ} (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    (C : ℝ) {k : ℕ} (hk : 1 ≤ k) (L : ℝ) :
    frequencyBudget Bs BD Bz k L k +
      (2-(3/4:ℝ)*Real.log ((2:ℝ)^k))*(2:ℝ)^k*(bulkSize k L:ℝ) +
      ((2:ℝ)^k*(initialGap Bs k L+C*(bulkSize k L:ℝ))+(bulkSize k L:ℝ))  ≤ 
    finalRate BD Bs Bz (C+2) k*(2:ℝ)^k*(bulkSize k L:ℝ)+
      (2:ℝ)^k*Real.sqrt (bulkSize k L)+(bulkSize k L:ℝ) := by
  have hlog := Real.log_nonneg (bulkScale_one_le hk)
  have hr : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnon : 0 ≤ ((2:ℝ)^k-1)*(Bs+8*Real.log (bulkScale k))*(bulkSize k L:ℝ)+
      (BD+Bz*Real.log (bulkScale k))*(bulkSize k L:ℝ)+
      (4/5:ℝ)*((2:ℝ)^k-1)*Real.log 2*(bulkSize k L:ℝ) := by positivity
  rw [frequencyBudget_eq]
  unfold finalRate initialGap
  nlinarith [hnon]

end Ostmann.Conclusion

end

end OAI
