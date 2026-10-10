import OAI.Combinatorics.ContingencyTables.Counting.CountingCoefficientBounds

namespace OAI

/-! # Polynomial numeric bounds for the three terminal controls -/

namespace ContingencyTables.CountingTerminalBounds
open Polynomial CountingCoefficientBounds
noncomputable section

def coefficientPolynomial : Polynomial ℕ := CountingCoefficientBounds.coefficientPolynomial.comp (2*X)
def gridPolynomial : Polynomial ℕ := 16*coefficientPolynomial*X^2
def cutoffPolynomial : Polynomial ℕ := 100*X*gridPolynomial
def phasePolynomial : Polynomial ℕ := 10*coefficientPolynomial*X^2*(cutoffPolynomial+1)

lemma coefficient_bound (L d E M : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) (hL : L ≤ M) (hd : d ≤ M) (hEM : E ≤ M) :
    CountingTerminalSchedule.coefficient L d (epsilon/2) ≤ coefficientPolynomial.eval M := by
  have hhalf : 1/(epsilon/2) ≤ ((2*E:ℕ):ℚ) := by
    have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 2 by norm_num)
    convert hh using 1 <;> push_cast <;> ring
  have hb := CountingCoefficientBounds.coefficient_polynomial L d (2*E) (2*M)
    (epsilon/2) (by positivity) hhalf (by omega) (by omega) (by omega)
  simpa only [coefficientPolynomial,eval_comp,eval_mul,eval_ofNat,eval_X] using hb

lemma terminal_bounds (C d W H M : ℕ)
    (hC : C ≤ coefficientPolynomial.eval M) (hd : d ≤ M)
    (hW : W=100*d*(16*C*d^2)) (hH : H=10*C*d^2*(W+1)) :
    16*C*d^2 ≤ gridPolynomial.eval M ∧
    W ≤ cutoffPolynomial.eval M ∧ H ≤ phasePolynomial.eval M := by
  have hgrid : 16*C*d^2 ≤ gridPolynomial.eval M := by
    simp only [gridPolynomial,eval_mul,eval_ofNat,eval_pow,eval_X]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 16 hC) (Nat.pow_le_pow_left hd 2)
  have hw : W ≤ cutoffPolynomial.eval M := by
    rw [hW]
    simp only [cutoffPolynomial,eval_mul,eval_ofNat,eval_X]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 100 hd) hgrid
  refine ⟨hgrid,hw,?_⟩
  rw [hH]
  simp only [phasePolynomial,eval_mul,eval_ofNat,eval_pow,eval_X,eval_add,eval_one]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul_left 10 hC) (Nat.pow_le_pow_left hd 2))
    (Nat.add_le_add_right hw 1)

end
end ContingencyTables.CountingTerminalBounds

end OAI
