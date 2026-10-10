import OAI.Algebra.FormulaHitting.Specification
import OAI.Algebra.FormulaHitting.Program
import OAI.Algebra.FormulaHitting.GeneratorCost
import OAI.Algebra.FormulaHitting.OutputBounds
import OAI.Algebra.FormulaHitting.BitCost

namespace OAI

namespace NCHittingSpecification

universe u

theorem dimension_eq (n s : ℕ) : dimension n s = NCHitting.dimension n s := rfl

theorem expectedEntry_eq (n s : ℕ) : expectedEntry n s = NCHitting.generator n s := rfl

theorem expectedProgram_eq : expectedProgram = NCHitting.generatorProgram := rfl

theorem execute_expectedProgram_eq (n s : ℕ) :
    NCHitting.BitModel.execute expectedProgram [n, s] = NCHitting.generate n s := rfl

theorem expectedOutput_eq (n s : ℕ) : expectedOutput n s = NCHitting.encodedOutput n s := rfl

theorem decode_eq : decode = NCHitting.decode := rfl

theorem entryBitBound_eq (n d : ℕ) : entryBitBound n d = NCHitting.entryBitBound n d := rfl

theorem costBound_eq (n s : ℕ) : costBound n s = NCHitting.generatorCostBound n s := rfl

theorem primitiveBitBound_eq (n s : ℕ) :
    primitiveBitBound n s = NCHitting.primitiveBitBound n s := rfl

theorem completeClaim_of_hitting {n s : ℕ} (hn : 1 ≤ n) (hs : 1 ≤ s)
    (hitting : UniversalHitting.{u} n s (dimension n s) (expectedEntry n s)) :
    CompleteClaim.{u} n s := by
  refine ⟨NCHitting.dimension_pos hn hs, NCHitting.dimension_le hn hs, ?_, ?_, ?_, ?_, ?_,
    ?_, hitting⟩
  · exact NCHitting.generate_output n s
  · exact NCHitting.generate_output_length n s
  · exact NCHitting.generate_entry_bounds
  · exact NCHitting.generate_entry_decode n s
  · exact NCHitting.generate_cost_le n s
  · exact NCHitting.generate_primitive_bit_bound n s

end NCHittingSpecification

end OAI
