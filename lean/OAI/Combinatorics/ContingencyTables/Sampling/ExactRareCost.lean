import OAI.Combinatorics.ContingencyTables.Sampling.ExactGatePolynomial

namespace OAI

/-! # Polynomial dependence of the correction cost on its finite tabulation measure -/

namespace ContingencyTables.ExactRareCost
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ProfilePrograms DensePrograms Polynomial
noncomputable section

attribute [local irreducible] ExactTypedProgram.program exactParsedMargins
  ExactGateCost.measure exactRareMeasure exactMatrixInput

def measure (z : CompletionMargins) : ℕ := ExactGateCost.measure z+exactRareMeasure z

theorem core_polynomial : ∃ p : Polynomial ℕ,∀ z,
    ExactCoreCost.budget z 1 ≤ p.eval (measure z) := by
  obtain ⟨g,hg⟩ := ExactGateCost.budget_polynomial
  obtain ⟨p,hp⟩ := work_exactMatrixInput
  obtain ⟨q,hq⟩ := ExactMatrixTrial.polynomial_trial
  refine ⟨g+p+q.comp p+12*p+C (weight (default : MatrixCode)+40),?_⟩
  intro z
  have hgate : ExactGatePrefix.budget z ≤ g.eval (measure z) :=
    (hg z).trans (polynomial_eval_monotone g (Nat.le_add_right _ _))
  have hmatrix : exactMatrixInputRealizer.cost z+weight (exactMatrixInput z) ≤ p.eval (measure z) :=
    (hp z).trans (polynomial_eval_monotone p (Nat.le_add_left _ _))
  have hw : weight (exactMatrixInput z) ≤ p.eval (measure z) :=
    (Nat.le_add_left _ _).trans hmatrix
  have htrial := (Nat.le_add_right _ _).trans
    ((hq (exactMatrixInput z)).trans (polynomial_eval_monotone q hw))
  change ExactMatrixTrial.trialRealizer.cost (exactMatrixInput z) ≤ q.eval (p.eval (measure z)) at htrial
  change rareBranchRealizer.cost z+exactOrdinaryRealizer.cost z+exactMatrixInputRealizer.cost z+
    1*(ExactMatrixTrial.trialRealizer.cost (exactMatrixInput z)+12*weight (exactMatrixInput z)+
      weight (default : MatrixCode)+40)+10*weight z+50 ≤ _
  change rareBranchRealizer.cost z+exactOrdinaryRealizer.cost z+10*weight z+50 ≤ _ at hgate
  simp only [eval_add,eval_mul,eval_ofNat,eval_C,eval_comp]
  omega

def publicMeasure (as : List Symbol) (B : ℕ) : ℕ :=
  weight as+measure (exactParsedMargins as)+B

/-- All copying and physical simulation costs are polynomial in the
already explicit finite-tabulation measure. -/
theorem public_polynomial : ∃ p : Polynomial ℕ,∀ as B,
    LiteralProgram.packTime as.length+ExactPhysicalCost.budget as 1 B+
      LiteralProgram.postTime B+1 ≤ p.eval (publicMeasure as B) := by
  obtain ⟨p,hp⟩ := polynomial_exactParsedMargins
  obtain ⟨q,hq⟩ := core_polynomial
  let t : Polynomial ℕ := p+q+X
  obtain ⟨v,hv⟩ := PhysicalCostPolynomial.bound
    (OnlineStack.accesses ExactTypedProgram.program.code)
    (OnlineStack.overhead ExactTypedProgram.program.code) t
  refine ⟨v+1,?_⟩
  intro as B
  let M := publicMeasure as B
  have hw : weight as ≤ M := by unfold M publicMeasure; omega
  have hg : measure (exactParsedMargins as) ≤ M := by unfold M publicMeasure; omega
  have hB : B ≤ M := by unfold M publicMeasure; omega
  have ht : ExactPhysicalCost.typedBudget as 1 B ≤ t.eval M := by
    have hp' := (Nat.le_add_right _ _).trans ((hp as).trans (polynomial_eval_monotone p hw))
    have hq' := (hq _).trans (polynomial_eval_monotone q hg)
    simpa only [ExactPhysicalCost.typedBudget,t,eval_add,eval_X] using
      Nat.add_le_add (Nat.add_le_add hp' hq') hB
  have hb := hv (weight as) (ExactPhysicalCost.typedBudget as 1 B) as.length B M hw ht
    ((list_length_le_weight as).trans hw) hB
  simpa only [ExactPhysicalCost.budget,OnlineStack.Executes.factor,eval_add,eval_one]
    using Nat.add_le_add_right hb 1

end
end ContingencyTables.ExactRareCost

end OAI
