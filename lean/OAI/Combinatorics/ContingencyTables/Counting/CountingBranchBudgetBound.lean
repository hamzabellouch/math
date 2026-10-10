import OAI.Combinatorics.ContingencyTables.Counting.CountingBranchSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectBudgetBound

namespace OAI

/-! # Combining the computed counting branches' public word budgets -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section

def budgetPolynomial (positivePolynomial : Polynomial ℕ) : Polynomial ℕ :=
  CountingDirectBudgetBound.budgetPolynomial+positivePolynomial

lemma publicBudget_bound (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (positive : Request→ℕ) (p : Polynomial ℕ)
    (hp : ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ),
      (∃ X,TableTightening.Feasible r c b X) → ∀ epsilon delta : ℚ,
      0 < epsilon → 0 < delta →
      positive (CountingDirectProgram.request r c b epsilon delta) ≤ p.eval (size r c b epsilon delta))
    (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0 < epsilon) (hd : 0 < delta) :
    publicBudget positive (Algorithms.encodeCountingInput r c b epsilon delta) ≤
      (budgetPolynomial p).eval (size r c b epsilon delta) := by
  have hrequest : request (CountingInputParser.parseInput
      (Algorithms.encodeCountingInput r c b epsilon delta))=
      CountingDirectProgram.request r c b epsilon delta := by
    rw [CountingInputParser.public_spec]
    rfl
  unfold publicBudget
  rw [hrequest]
  by_cases hf : feasible (CountingDirectProgram.request r c b epsilon delta)=true
  · have hne := (feasible_data hEK r c b epsilon delta).mp hf
    by_cases hz : direct (CountingDirectProgram.request r c b epsilon delta)=true
    · rw [budget_direct positive _ hf hz]
      exact (CountingDirectBudgetBound.budget_public hEK r c b hne epsilon delta he hd).trans
        (by simp only [budgetPolynomial,Polynomial.eval_add]; omega)
    · have hz' : direct (CountingDirectProgram.request r c b epsilon delta)=false :=
        Bool.eq_false_iff.mpr hz
      rw [budget_positive positive _ hf hz']
      exact (hp m n r c b hne epsilon delta he hd).trans
        (by simp only [budgetPolynomial,Polynomial.eval_add]; omega)
  · have hf' : feasible (CountingDirectProgram.request r c b epsilon delta)=false :=
      Bool.eq_false_iff.mpr hf
    rw [budget_rejected positive _ hf']
    exact Nat.zero_le _

end
end ContingencyTables.CountingBranchProgram

end OAI
