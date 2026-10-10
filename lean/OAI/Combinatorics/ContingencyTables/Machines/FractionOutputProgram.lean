import OAI.Combinatorics.MatchingCount.Complexity.TreeFractionCosts
import OAI.Combinatorics.MatchingCount.Tapes.Codec

namespace OAI

/-! # Canonical nonnegative rational output on the public tape -/

namespace ContingencyTables.FractionOutputProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec

def output (x : TreeFraction.Fraction) : List Symbol := ratWord (TreeFraction.normalize x)
def outputRealizer : Realizer output :=
  composition (f := TreeFraction.normalize) (g := ratWord)
    TreeFraction.normalizeRealizer ratWordRealizer
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition TreeFraction.polynomial_normalize polynomial_ratWord

lemma output_eq (x : TreeFraction.Fraction) : output x=encodeRat (TreeFraction.val x) := by
  rw [output,TreeFraction.normalize_repr,ratWord_repr _ (TreeFraction.val_nonneg x)]

lemma natWord_symbols (n : ℕ) (a : Symbol) (ha : a∈natWord n) : a≠0 ∧ a≠6 ∧ a≠7 := by
  simp only [natWord,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩ | rfl
  · cases b <;> decide
  · decide

lemma output_symbols (x : TreeFraction.Fraction) (a : Symbol) (ha : a∈output x) :
    a≠0 ∧ a≠6 ∧ a≠7 := by
  simp only [output,ratWord,List.mem_cons,List.mem_append] at ha
  rcases ha with (rfl | ha) | ha
  · decide
  · exact natWord_symbols _ a ha
  · exact natWord_symbols _ a ha

end ContingencyTables.FractionOutputProgram

end OAI
