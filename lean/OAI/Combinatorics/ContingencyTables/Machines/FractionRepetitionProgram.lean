import OAI.Combinatorics.ContingencyTables.Counting.CountingOracleScheduleProgram
import OAI.Combinatorics.ContingencyTables.Transport.FiniteMedianConfidence

namespace OAI

/-! # Executing the confidence repetition count on a rational input -/
namespace ContingencyTables.FractionRepetitionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

def count (x : TreeFraction.Fraction) : ℕ := 64*((TreeFraction.normalize x).2.bits.length+1)
def countRealizer : Realizer count :=
  composition (f := fun x : TreeFraction.Fraction => (64,(TreeFraction.normalize x).2.bits.length+1))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (constant 64) (composition
      (composition (composition (composition TreeFraction.normalizeRealizer second) toBits) listLength)
      successor)) multiply
lemma polynomial_count : PolynomialTime countRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 64)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition TreeFraction.polynomial_normalize polynomial_second) polynomial_toBits)
      polynomial_listLength) polynomial_successor)) polynomial_multiply
lemma count_val (x : TreeFraction.Fraction) : count x=CommonBasesFPRAS.repetitionCount (TreeFraction.val x) := by
  simp only [count,TreeFraction.normalize_repr,TreeFraction.repr,CommonBasesFPRAS.repetitionCount]
end ContingencyTables.FractionRepetitionProgram

end OAI
