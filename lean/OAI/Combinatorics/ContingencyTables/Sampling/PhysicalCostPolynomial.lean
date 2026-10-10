import OAI.Combinatorics.ContingencyTables.Machines.LiteralProgram
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomial

namespace OAI

/-! # Polynomial arithmetic for the physical compiler's explicit cost -/

namespace ContingencyTables.PhysicalCostPolynomial
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
noncomputable section

theorem bound (a o : ℕ) (t : Polynomial ℕ) : ∃ p : Polynomial ℕ,
    ∀ H C N B M : ℕ,H ≤ M → C ≤ t.eval M → N ≤ M → B ≤ M →
      LiteralProgram.packTime N+C*(o*(1+2*a*(H+C*a+1))+1)+LiteralProgram.postTime B ≤
        p.eval M := by
  let fac : Polynomial ℕ := C o*(1+2*C a*(X+t*C a+1))+1
  let pk : Polynomial ℕ := (1+LiteralProgram.budgetPolynomial 1 (18*LiteralPacked.width) X 0)*
    C (MachineCost.programCost LiteralPacked.packCode)
  let out : Polynomial ℕ := C (MachineCost.programCost (LiteralTape.eraseCode LiteralPacked.header.length))+
    (1+LiteralProgram.budgetPolynomial (18*LiteralPacked.width) 1 X 0)*
      C (MachineCost.programCost LiteralPacked.unpackCode)
  refine ⟨pk+t*fac+out,?_⟩
  intro H K N B M hH hK hN hB
  have hf : o*(1+2*a*(H+K*a+1))+1 ≤ fac.eval M := by
    simp only [fac,eval_add,eval_mul,eval_C,eval_ofNat,eval_X,eval_one]
    gcongr
  have hpk : pk.eval M=LiteralProgram.packTime M := by
    simp only [pk,eval_mul,eval_add,eval_one,eval_C,LiteralProgram.eval_budgetPolynomial,
      eval_X,eval_zero,LiteralProgram.packTime]
  have hout : out.eval M=LiteralProgram.postTime M := by
    simp only [out,eval_add,eval_mul,eval_one,eval_C,LiteralProgram.eval_budgetPolynomial,
      eval_X,eval_zero,LiteralProgram.postTime]
  simp only [eval_add,eval_mul,hpk,hout]
  exact Nat.add_le_add (Nat.add_le_add (LiteralProgram.packTime_mono hN)
    (Nat.mul_le_mul hK hf)) (LiteralProgram.postTime_mono hB)

end
end ContingencyTables.PhysicalCostPolynomial

end OAI
