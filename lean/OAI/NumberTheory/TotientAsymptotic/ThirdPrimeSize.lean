import OAI.NumberTheory.TotientAsymptotic.FordCoordinateBounds

namespace OAI

/-! The complement of the two-coordinate exception has a small third prime. -/
noncomputable section
namespace TotientAsymptotic

lemma ford_coordinate_antitone (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    fordPrimeCoordinate n j ≤ fordPrimeCoordinate n i := by
  by_cases hj : j < n.primeFactorsList.length
  · have hi : i < n.primeFactorsList.length := by omega
    have hp := fordPrime_prime hj
    have horder := fordPrime_antitone hi hj hij
    have hB : primeDoubleLog n j ≤ primeDoubleLog n i :=
      Real.log_le_log (Real.log_pos (by exact_mod_cast hp.one_lt))
        (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast horder))
    exact max_le_max le_rfl hB
  · have he : fordPrime n j=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hj)]
      rfl
    simp only [fordPrimeCoordinate,primeDoubleLog,he,Nat.cast_one,Real.log_one,Real.log_zero,max_self]
    exact le_max_left _ _

lemma third_coordinate_bound {x : ℝ} {n : ℕ}
    (hscore : a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x) :
    fordPrimeCoordinate n 2 ≤ (4/5:ℝ)*B x := by
  have ha := first_two_a_bounds
  have hsum : (32/25:ℝ) ≤ a 1+a 2 := by
    have he : a 1+a 2=3*Real.log 3-2 := by norm_num [a]; ring
    rw [he]
    linarith [Real.log_three_gt_d9]
  have horder := ford_coordinate_antitone n (show 1 ≤ 2 by norm_num)
  have hnon : 0 ≤ fordPrimeCoordinate n 2 := le_max_left _ _
  have h1 := mul_le_mul_of_nonneg_left horder ha.1.le
  have h2 := mul_le_mul_of_nonneg_right hsum hnon
  nlinarith only [hscore,h1,h2,hnon]

lemma third_prime_size {x : ℝ} {n : ℕ} (hx : 1 < x)
    (hscore : a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x) :
    (fordPrime n 2:ℝ) ≤ Real.exp ((Real.log x)^(4/5:ℝ)) := by
  have hcoord := third_coordinate_bound hscore
  have hraw : B (fordPrime n 2) ≤ (4/5:ℝ)*B x := (le_max_right _ _).trans hcoord
  by_cases hi : 2 < n.primeFactorsList.length
  · have hp := fordPrime_prime hi
    have hplog : 0 < Real.log (fordPrime n 2) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hxp : 0 < Real.log x := Real.log_pos hx
    have hh := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hraw)
    rw [B,Real.exp_log hplog,Real.exp_log (by exact_mod_cast hp.pos)] at hh
    convert hh using 1
    rw [Real.rpow_def_of_pos hxp]
    congr 2
    unfold B
    ring
  · have he : fordPrime n 2=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]
      rfl
    rw [he,Nat.cast_one]
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_pos hx).le _)

end TotientAsymptotic

end

end OAI
