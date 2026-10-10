import OAI.NumberTheory.TotientAsymptotic.RenewalMagnitude

namespace OAI

/-! Concrete concavity of the coefficients in Ford's renewal recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma a_shift_integral (j k : ℕ) :
    a (j+k)=∫ t in (j : ℝ)..(j+1 : ℝ), Real.log (t+k) := by
  rw [a_eq_integral,intervalIntegral.integral_comp_add_right]
  push_cast
  congr 1
  ring

lemma log_shift_intervalIntegrable {j : ℕ} (hj : 1≤j) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => Real.log (t+k)) MeasureTheory.volume j (j+1) := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
  intro t ht
  have hn : t+(k : ℝ)≠0 := by
    have hk : (0 : ℝ)≤k := Nat.cast_nonneg _
    linarith [ht.1]
  exact ((continuousAt_id.add continuousAt_const).log hn).continuousWithinAt

lemma log_second_difference_pos {t : ℝ} (ht : 0<t) :
    0<2*Real.log (t+1)-(Real.log t+Real.log (t+2)) := by
  have ht2 : 0<t+2 := by linarith
  have hh := Real.log_lt_log (mul_pos ht ht2)
    (show t*(t+2)<(t+1)^2 by nlinarith)
  rw [Real.log_mul ht.ne' ht2.ne',Real.log_pow] at hh
  norm_num at hh
  linarith

/-- The strict second difference used in Ford Lemma 3.7. -/
lemma a_second_difference_neg {j : ℕ} (hj : 1≤j) :
    a (j+2)-2*a (j+1)+a j<0 := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  have hc : ContinuousOn
      (fun t : ℝ => 2*Real.log (t+1)-(Real.log t+Real.log (t+2)))
      (Set.Icc (j : ℝ) (j+1)) := by
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    have ht1 : t+1≠0 := by linarith [ht.1]
    have ht2 : t+2≠0 := by linarith [ht.1]
    exact ((continuousAt_const.mul ((continuousAt_id.add continuousAt_const).log ht1)).sub
      ((continuousAt_id.log ht0).add ((continuousAt_id.add continuousAt_const).log ht2))).continuousWithinAt
  have hi : 0<∫ t in (j : ℝ)..(j+1 : ℝ),
      2*Real.log (t+1)-(Real.log t+Real.log (t+2)) := by
    apply intervalIntegral.integral_pos (by linarith) hc
    · intro t ht
      exact (log_second_difference_pos (by linarith [ht.1])).le
    · refine ⟨j+1,⟨by linarith,le_rfl⟩,?_⟩
      exact log_second_difference_pos (by linarith)
  have h0 := log_shift_intervalIntegrable hj 0
  have h1 := log_shift_intervalIntegrable hj 1
  have h2 := log_shift_intervalIntegrable hj 2
  have he1 := a_shift_integral j 1
  have he2 := a_shift_integral j 2
  simp only [Nat.cast_one,Nat.cast_ofNat] at h1 h2 he1 he2
  simp only [Nat.cast_zero,add_zero] at h0
  rw [intervalIntegral.integral_sub (h1.const_mul 2) (h0.add h2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_add h0 h2,
    ← he1,← he2,← a_eq_integral j] at hi
  linarith

end TotientAsymptotic

end

end OAI
