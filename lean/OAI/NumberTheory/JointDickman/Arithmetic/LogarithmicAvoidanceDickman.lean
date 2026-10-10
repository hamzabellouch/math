import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicAvoidanceRecurrence
import OAI.NumberTheory.JointDickman.Arithmetic.DickmanReciprocalIntegral

namespace OAI

/-! # Identifying the ordered inclusion-exclusion integrals with Dickman rho -/
namespace JointDickman
open MeasureTheory Erdos970.NumberTheoryLean

 theorem logarithmicAvoidance_eq_dickman (N : ℕ) {c : ℝ} (hc : 0 < c)
    (hN : 1/c ≤ (N : ℝ)+1) :
    logarithmicAvoidance N c = Dickman.rho (1/c) := by
  induction N generalizing c with
  | zero =>
    rw [logarithmicAvoidance_zero, Dickman.rho_initial (by simpa using hN)]
  | succ N ih =>
    by_cases hc1 : 1 ≤ c
    · rw [logarithmicAvoidance_initial hc1, Dickman.rho_initial]
      exact (div_le_one hc).mpr hc1
    · have hc1' : c ≤ 1 := (lt_of_not_ge hc1).le
      rw [logarithmicAvoidance_succ hc hc1', dickman_reciprocal_integral hc hc1']
      congr 1
      apply intervalIntegral.integral_congr_Ioo_of_le hc1'
      intro s hs
      dsimp only
      have hs0 : 0 < s := hc.trans hs.1
      have hd : 0 < 1-s := sub_pos.mpr hs.2
      have he : 1/(s/(1-s)) = 1/s-1 := by
        field_simp
      have hb : 1/(s/(1-s)) ≤ (N : ℝ)+1 := by
        rw [he]
        have hinv := one_div_le_one_div_of_le hc hs.1.le
        push_cast at hN
        linarith
      rw [ih (div_pos hs0 hd) hb, he]

end JointDickman

end OAI
