import OAI.Combinatorics.ContingencyTables.Sampling.ExactGatePrefix

namespace OAI

/-! # Polynomial cost before the rare branch starts -/

namespace ContingencyTables.ExactGateCost
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

def measure (z : CompletionMargins) : ℕ :=
  exactParameterMeasure z+FiniteWordExecution.wordMeasure exactOrdinaryBits z

lemma budget_polynomial : ∃ p : Polynomial ℕ,
    ∀ z,ExactGatePrefix.budget z ≤ p.eval (measure z) := by
  obtain ⟨p,hp⟩ := work_rareBranch
  obtain ⟨q,hq⟩ := work_exactOrdinary
  refine ⟨p+q+10*X+50,?_⟩
  intro z
  have h1 : rareBranchRealizer.cost z ≤ p.eval (measure z) :=
    (Nat.le_add_right _ _).trans ((hp z).trans (polynomial_eval_monotone p (Nat.le_add_right _ _)))
  have h2 : exactOrdinaryRealizer.cost z ≤ q.eval (measure z) :=
    (Nat.le_add_right _ _).trans ((hq z).trans (polynomial_eval_monotone q (Nat.le_add_left _ _)))
  have h3 : weight z ≤ measure z := by unfold measure exactParameterMeasure; omega
  change rareBranchRealizer.cost z+exactOrdinaryRealizer.cost z+10*weight z+50 ≤ _
  simp only [eval_add,eval_mul,eval_ofNat,eval_X]
  omega

end ContingencyTables.ExactGateCost

end OAI
