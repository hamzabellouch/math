import OAI.NumberTheory.Ostmann.Conclusion.BadArrangementCount

namespace OAI

noncomputable section
namespace Ostmann.Conclusion

theorem log_factorial_lower {n : ℕ} (hn : 0 < n) :
    (n : ℝ)*Real.log n-n ≤ Real.log (n.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (Nat.ne_of_gt hn)
  have hnlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hpi : 0 ≤ Real.log (2*Real.pi) := by
    apply Real.log_nonneg
    have := Real.pi_gt_three
    linarith
  linarith

theorem log_factorial_upper {n : ℕ} (_hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ)*Real.log n := by
  have hcast : (n.factorial : ℝ) ≤ (n : ℝ)^n := by exact_mod_cast n.factorial_le_pow
  have h := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial) hcast
  simpa only [Real.log_pow] using h

theorem factorial_ratio_bound {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    (m.factorial : ℝ)^r / ((r*m).factorial : ℝ) ≤
      Real.exp ((1-Real.log r)*(r : ℝ)*m) := by
  have hp : (0 : ℝ) < (m.factorial : ℝ)^r / ((r*m).factorial : ℝ) := by positivity
  apply (Real.log_le_iff_le_exp hp).mp
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  have hlo := log_factorial_lower (Nat.mul_pos hr hm)
  have hup := mul_le_mul_of_nonneg_left (log_factorial_upper hm)
    (show 0 ≤ (r : ℝ) by positivity)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [Nat.cast_mul, Real.log_mul hr0 hm0] at hlo
  nlinarith

theorem badArrangement_fraction_bound {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    (badArrangementCount r m : ℝ) / ((r*m).factorial : ℝ) ≤
      (r : ℝ)^(2*r) * Real.exp (((5/4 : ℝ)-(3/4 : ℝ)*Real.log r)*(r : ℝ)*m) := by
  have hden : (0 : ℝ) < (r*m).factorial := by positivity
  calc
    _ ≤ ((r : ℝ)^(2*r)*((m.factorial : ℝ)^r*
        Real.exp ((Real.log r+1)*(r : ℝ)*m/4))) / ((r*m).factorial : ℝ) :=
      div_le_div_of_nonneg_right (badArrangementCount_le hr hm) hden.le
    _ = (r : ℝ)^(2*r)*Real.exp ((Real.log r+1)*(r : ℝ)*m/4)*
        ((m.factorial : ℝ)^r/((r*m).factorial : ℝ)) := by ring
    _ ≤ (r : ℝ)^(2*r)*Real.exp ((Real.log r+1)*(r : ℝ)*m/4)*
        Real.exp ((1-Real.log r)*(r : ℝ)*m) := by
      exact mul_le_mul_of_nonneg_left (factorial_ratio_bound hr hm) (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end Ostmann.Conclusion

end

end OAI
