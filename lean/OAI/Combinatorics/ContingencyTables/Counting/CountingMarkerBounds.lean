import OAI.Combinatorics.ContingencyTables.Counting.CountingOracleWordBounds
import OAI.Combinatorics.ContingencyTables.Transport.PowerOfTwoApproximation

namespace OAI

/-! # Polynomial space for the executed power-approximation markers -/
namespace ContingencyTables.CountingMarkerBounds
open CompanionOracleDensity Polynomial
noncomputable section

def paddingPolynomial : Polynomial ℕ := 409600*(X+1)*X

lemma inner_inverse_bound (j M : ℕ) (xi : ℚ) (hj : j ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ)) :
    1/innerTolerance (xi/2) j ≤ ((400*(M+1)*M:ℕ):ℚ) := by
  have heq : 1/innerTolerance (xi/2) j=(400:ℚ)*(j+1)*(1/xi) := by
    unfold innerTolerance
    field_simp
    ring
  rw [heq]
  have hh := mul_le_mul
    (show (400:ℚ)*(j+1) ≤ 400*(M+1) by exact_mod_cast Nat.mul_le_mul_left 400 (Nat.add_le_add_right hj 1))
    hi (one_div_pos.mpr hxi).le (by positivity)
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hh

lemma degree_bound (j M : ℕ) (xi : ℚ) (hj : j ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ)) :
    PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)) ≤
      512*(400*(M+1)*M) := by
  unfold PowerOfTwoApproximation.rootDegree roundingTolerance
  apply Nat.ceil_le.mpr
  have hh := mul_le_mul_of_nonneg_left (inner_inverse_bound j M xi hj hxi hi)
    (show (0:ℚ) ≤ 512 by norm_num)
  convert hh using 1
  · field_simp
    ring
  · push_cast
    rfl

lemma padding_bound (j M : ℕ) (xi : ℚ) (hj : j ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ)) :
    PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j))+
      PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)) ≤
        paddingPolynomial.eval M := by
  have hd := degree_bound j M xi hj hxi hi
  have hdepth : PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)) ≤
      PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)) :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  simp only [paddingPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  have heq : 409600*(M+1)*M=2*(512*(400*(M+1)*M)) := by ring
  rw [heq]
  omega

end
end ContingencyTables.CountingMarkerBounds

end OAI
