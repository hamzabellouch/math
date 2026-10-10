import OAI.Combinatorics.ContingencyTables.Sampling.ExactInputBounds
import OAI.Combinatorics.ContingencyTables.Sampling.ExactGatePublic
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalCostPolynomial

namespace OAI

/-! # A uniform polynomial bound for the cheap public prefix -/

namespace ContingencyTables.ExactGatePolynomial
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ProfilePrograms DensePrograms Polynomial
open Algorithms (samplingSize encodeMargins)
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] ExactTypedProgram.program exactParsedMargins
  ExactGatePrefix.budget ExactGateCost.measure

def measure (as : List Symbol) (B : ℕ) : ℕ :=
  weight as+ExactGateCost.measure (exactParsedMargins as)+B

theorem budget_polynomial : ∃ p : Polynomial ℕ,∀ as B,
    LiteralProgram.packTime as.length+ExactGatePhysical.budget as B+LiteralProgram.postTime B ≤
      p.eval (measure as B) := by
  obtain ⟨p,hp⟩ := polynomial_exactParsedMargins
  obtain ⟨q,hq⟩ := ExactGateCost.budget_polynomial
  let t : Polynomial ℕ := p+q+X
  obtain ⟨v,hv⟩ := PhysicalCostPolynomial.bound
    (OnlineStack.accesses ExactTypedProgram.program.code)
    (OnlineStack.overhead ExactTypedProgram.program.code) t
  refine ⟨v,?_⟩
  intro as B
  let M := measure as B
  have hw : weight as ≤ M := by unfold M measure; omega
  have hg : ExactGateCost.measure (exactParsedMargins as) ≤ M := by unfold M measure; omega
  have hB : B ≤ M := by unfold M measure; omega
  have ht : ExactGatePhysical.typedBudget as B ≤ t.eval M := by
    have hp' := (Nat.le_add_right _ _).trans ((hp as).trans (polynomial_eval_monotone p hw))
    have hq' := (hq _).trans (polynomial_eval_monotone q hg)
    simpa only [ExactGatePhysical.typedBudget,t,eval_add,eval_X] using
      Nat.add_le_add (Nat.add_le_add hp' hq') hB
  have hb := hv (weight as) (ExactGatePhysical.typedBudget as B) as.length B M hw ht
    ((list_length_le_weight as).trans hw) hB
  simpa only [ExactGatePhysical.budget,OnlineStack.Executes.factor] using hb

/-- Any fixed polynomial print allowance still gives a uniform public
polynomial bound for the prefix before the rare tabulation starts. -/
theorem public_bound (print : Polynomial ℕ) : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j →
      let B := print.eval (ExactPrintCost.matrixSize (n := n) r)
      ExactGatePublic.budget r c B B ≤ p.eval (samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := budget_polynomial
  obtain ⟨q,hq⟩ := SmallGraphProfiles.exact_gate_measure_polynomial
  let u : Polynomial ℕ := 91*X^2+q+print.comp (25*X^3)
  refine ⟨p.comp u,?_⟩
  intro m n r c htotal
  dsimp only
  have hm : measure (encodeMargins r c) (print.eval (ExactPrintCost.matrixSize (n := n) r)) ≤
      u.eval (samplingSize n r 0) := by
    simp only [measure,SmallGraphProfiles.exactParsedMargins_spec,u,eval_add,eval_mul,
      eval_ofNat,eval_pow,eval_X,eval_comp]
    exact Nat.add_le_add (Nat.add_le_add (SmallGraphProfiles.exact_public_weight r c htotal)
      (hq m n r c htotal))
      (polynomial_eval_monotone print (SmallGraphProfiles.exact_matrix_size (n := n) r))
  have hb : LiteralProgram.packTime (encodeMargins r c).length+
      ExactGatePhysical.budget (encodeMargins r c) (print.eval (ExactPrintCost.matrixSize (n := n) r))+
      LiteralProgram.postTime (print.eval (ExactPrintCost.matrixSize (n := n) r)) ≤
      (p.comp u).eval (samplingSize n r 0) :=
    (hp (encodeMargins r c) (print.eval (ExactPrintCost.matrixSize (n := n) r))).trans (by
    rw [eval_comp]
    exact polynomial_eval_monotone p hm)
  simpa only [ExactGatePublic.budget,ExactTablePrefix.input] using hb

end
end ContingencyTables.ExactGatePolynomial

end OAI
