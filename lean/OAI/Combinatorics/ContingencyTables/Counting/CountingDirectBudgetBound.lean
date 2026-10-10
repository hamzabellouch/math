import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectWordBound
import OAI.Combinatorics.ContingencyTables.Counting.CountingMarkerBounds

namespace OAI

/-! # Public runtime allowance for the direct branch's padded random word -/
namespace ContingencyTables.CountingDirectBudgetBound
open Polynomial CountingPublicInputBounds
open scoped Classical
noncomputable section
variable {m n : ℕ}

def budgetPolynomial : Polynomial ℕ := CountingDirectWordBound.wordPolynomial+
  CountingMarkerBounds.paddingPolynomial.comp CountingDirectWordBound.controlPolynomial

lemma budget_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    CountingDirectProgram.budget (CountingDirectProgram.request r c b epsilon delta) ≤
      budgetPolynomial.eval (size r c b epsilon delta) := by
  let S := size r c b epsilon delta
  let M := CountingDirectWordBound.controlPolynomial.eval S
  have hH : ComputedCountingParameters.phases r c b epsilon ≤ M := by
    have hb : CountingTerminalBounds.phasePolynomial.eval S ≤ M := by
      simp only [M,CountingDirectWordBound.controlPolynomial,CountingPublicWordBound.controlPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
      omega
    exact (CountingPublicTerminalBounds.terminal_public hEK r c b hne epsilon delta he).2.2.trans hb
  have h4S : 4*S ≤ M := by
    simp only [M,CountingDirectWordBound.controlPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  have hi : 1/((epsilon/2)/2) ≤ (M:ℚ) := by
    have hh := mul_le_mul_of_nonneg_left (inverse_le r c b epsilon delta)
      (show (0:ℚ) ≤ 4 by norm_num)
    have hh' : 1/((epsilon/2)/2) ≤ ((4*S:ℕ):ℚ) := by
      convert hh using 1 <;> push_cast <;> ring
    exact hh'.trans (by exact_mod_cast h4S)
  have hp := CountingMarkerBounds.padding_bound
    (ComputedCountingParameters.phases r c b epsilon) M ((epsilon/2)/2) hH (by positivity) hi
  rw [CountingDirectProgram.budget_data hEK r c b hne epsilon delta he hd]
  have hw := CountingDirectWordBound.zeroBits_public hEK r c b hne epsilon delta he
  rw [Nat.add_assoc]
  simpa only [budgetPolynomial,Polynomial.eval_add,Polynomial.eval_comp,
    CountingDirectProgram.degree,CountingDirectProgram.depth,S,M] using Nat.add_le_add hw hp

end
end ContingencyTables.CountingDirectBudgetBound

end OAI
