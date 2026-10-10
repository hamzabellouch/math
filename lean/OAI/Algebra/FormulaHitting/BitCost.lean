import OAI.Algebra.FormulaHitting.GeneratorCost
import OAI.Algebra.FormulaHitting.BitRefinement

namespace OAI

namespace NCHitting

def primitiveBitBound (n s : ℕ) : ℕ := 1024 * generatorCostBound n s ^ 3

def generatorBitTrace (n s : ℕ) : BitRefinement.Trace :=
  BitRefinement.Step.input [n, s] :: BitRefinement.programTrace [n, s] generatorProgram

theorem generatorBitTrace_executes (n s : ℕ) :
    BitRefinement.Exec generatorProgram [n, s] (generate n s).output
      (BitRefinement.Trace.steps (generatorBitTrace n s)) :=
  ⟨BitRefinement.programTrace [n, s] generatorProgram,
    BitRefinement.programTrace_correct [n, s] generatorProgram, rfl⟩

theorem generate_primitive_bit_bound (n s : ℕ) :
    BitRefinement.Exec generatorProgram [n, s] (generate n s).output
        (BitRefinement.executionSteps generatorProgram [n, s]) ∧
      BitRefinement.executionSteps generatorProgram [n, s] ≤ primitiveBitBound n s := by
  refine ⟨BitRefinement.executionSteps_exec generatorProgram [n, s],
    (BitRefinement.executionSteps_le generatorProgram [n, s]).trans ?_⟩
  exact Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left (generate_cost_le n s) 3)

end NCHitting

end OAI
