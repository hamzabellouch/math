import OAI.Combinatorics.ContingencyTables.Counting.CountingTerminalSchedule
import OAI.Combinatorics.ContingencyTables.Counting.CountingScheduleSizes

namespace OAI

/-! # Numeric polynomial bounds for the computed terminal coefficient -/

namespace ContingencyTables.CountingCoefficientBounds
open CountingTerminalSchedule
noncomputable section

lemma precision_le (epsilon : ℚ) (E : ℕ) (hE : 1/epsilon ≤ (E:ℚ)) :
    precision epsilon ≤ E := by
  unfold precision
  have hc : ⌈1/epsilon⌉₊ ≤ E := Nat.ceil_le.mpr hE
  exact Nat.clog_le_of_le_pow (hc.trans (Nat.lt_two_pow_self.le))

lemma allowance_le (L d E : ℕ) (epsilon : ℚ) (hE : 1/epsilon ≤ (E:ℚ)) :
    allowance L d epsilon ≤ 20*(L+d+E+1) := by
  have hp := precision_le epsilon E hE
  unfold allowance
  omega

lemma coefficient_le (L d E : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) :
    coefficient L d epsilon ≤ 2048*d*(20*(L+d+E+1))^2*E := by
  apply Nat.ceil_le.mpr
  have ha := allowance_le L d E epsilon hE
  have haQ : (allowance L d epsilon:ℚ) ≤ (20*(L+d+E+1):ℕ) := by exact_mod_cast ha
  have hs : (allowance L d epsilon:ℚ)^2 ≤ ((20*(L+d+E+1):ℕ):ℚ)^2 := by
    have ha0 : (0:ℚ) ≤ allowance L d epsilon := Nat.cast_nonneg _
    nlinarith
  have hm := mul_le_mul hs hE (one_div_pos.mpr he).le (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hm (show (0:ℚ) ≤ 2048*d by positivity)
  convert hmul using 1 <;> push_cast <;> ring

open Polynomial

def coefficientPolynomial : Polynomial ℕ := 2048*X*(20*(3*X+1))^2*X

lemma coefficient_polynomial (L d E M : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) (hL : L ≤ M) (hd : d ≤ M) (hEM : E ≤ M) :
    coefficient L d epsilon ≤ coefficientPolynomial.eval M := by
  have hb := coefficient_le L d E epsilon he hE
  have ha : 20*(L+d+E+1) ≤ 20*(3*M+1) := by omega
  have ht : 2048*d*(20*(L+d+E+1))^2*E ≤ 2048*M*(20*(3*M+1))^2*M :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2048 hd)
      (Nat.pow_le_pow_left ha 2)) hEM
  exact hb.trans (by simpa only [coefficientPolynomial,eval_mul,eval_ofNat,eval_X,
    eval_pow,eval_add,eval_one] using ht)

end
end ContingencyTables.CountingCoefficientBounds

end OAI
