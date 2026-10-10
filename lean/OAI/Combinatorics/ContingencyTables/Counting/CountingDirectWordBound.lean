import OAI.Combinatorics.ContingencyTables.Counting.CountingPublicWordBound
import OAI.Combinatorics.ContingencyTables.Counting.ComputedCountingZero

namespace OAI

/-! # Public word budget for the direct zero-label estimator -/
namespace ContingencyTables.CountingDirectWordBound
open CompanionFactorialApplication CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def controlPolynomial : Polynomial ℕ := CountingPublicWordBound.controlPolynomial+4*X
def wordPolynomial : Polynomial ℕ := CountingOracleWordBounds.medianPolynomial.comp controlPolynomial

lemma zeroBits_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta ≤
      wordPolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let C := ComputedCountingParameters.coefficient r c b epsilon
  let K := ComputedCountingParameters.binCount r c b epsilon
  let H := ComputedCountingParameters.phases r c b epsilon
  let S := size r c b epsilon delta
  let M := controlPolynomial.eval S
  have hSM : S ≤ M := by
    simp only [M,controlPolynomial,CountingPublicWordBound.controlPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hKM : CountingTerminalBounds.gridPolynomial.eval S ≤ M := by
    simp only [M,controlPolynomial,CountingPublicWordBound.controlPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hHM : CountingTerminalBounds.phasePolynomial.eval S ≤ M := by
    simp only [M,controlPolynomial,CountingPublicWordBound.controlPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have h4SM : 4*S ≤ M := by
    simp only [M,controlPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  have ht := CountingPublicTerminalBounds.terminal_public hEK r c b hne epsilon delta he
  have hd : A.d ≤ M := (dimension_le r c b epsilon delta).trans hSM
  have hK : K ≤ M := ht.1.trans hKM
  have hH : H ≤ M := ht.2.2.trans hHM
  have hL : CountingTerminalSchedule.capacityBits A ≤ M :=
    (capacityBits_le hEK r c b hne epsilon delta).trans hSM
  have hi : 1/((epsilon/2)/2) ≤ (M:ℚ) := by
    have hh := mul_le_mul_of_nonneg_left (inverse_le r c b epsilon delta)
      (show (0:ℚ) ≤ 4 by norm_num)
    have hh' : 1/((epsilon/2)/2) ≤ ((4*S:ℕ):ℚ) := by
      convert hh using 1 <;> push_cast <;> ring
    exact hh'.trans (by exact_mod_cast h4SM)
  have hr : CommonBasesFPRAS.repetitionCount delta ≤ 64*(M+1) :=
    (repeats_le r c b epsilon delta).trans (Nat.mul_le_mul_left 64 (by omega))
  have hb := CountingOracleWordBounds.median_bound_separate A C K H M ((epsilon/2)/2) delta
    hd hK hH hH hL (by positivity) hi hr
  unfold ComputedCountingZero.zeroBits
  rw [←ComputedCountingParameters.phases_final hEK r c b hne epsilon he]
  simpa only [wordPolynomial,Polynomial.eval_comp] using hb

end
end ContingencyTables.CountingDirectWordBound

end OAI
