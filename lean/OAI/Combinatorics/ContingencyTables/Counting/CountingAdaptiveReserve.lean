import OAI.Combinatorics.ContingencyTables.Counting.CountingAdaptiveInputProgram

namespace OAI

/-! # The initializer uses only the length of its reserved word -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS

lemma zeroCode_eq_of_length_eq (x : CountingBaseProgram.Input) (a b : List Bool)
    (h : a.length=b.length) : zeroCode (x,a)=zeroCode (x,b) := by
  simp only [zeroCode,List.map_const',List.length_take,labelWidth,h]

lemma initialInput_eq_of_length_eq (x : CountingBaseProgram.Input) (a b : List Bool)
    (h : a.length=b.length) : initialInput (x,a)=initialInput (x,b) := by
  change (CountingPreparedState.catalog x,(capacities (x,a),zeroCode (x,a)))=
    (CountingPreparedState.catalog x,(capacities (x,b),zeroCode (x,b)))
  rw [zeroCode_eq_of_length_eq x a b h]
  rfl

theorem output_eq_of_length_eq (x : CountingBaseProgram.Input) (a b : List Bool)
    (h : a.length=b.length) : output (x,a)=output (x,b) := by
  have hi := initialInput_eq_of_length_eq x a b h
  apply Prod.ext
  · rfl
  · exact congrArg CompanionInitialStoredProgram.output hi

theorem output_ofFn (x : CountingBaseProgram.Input) (N : ℕ) (bits : Fin N→Bool) :
    output (x,List.ofFn bits)=output (x,List.replicate N false) :=
  output_eq_of_length_eq x _ _ (by simp only [List.length_ofFn,List.length_replicate])

end ContingencyTables.CountingAdaptiveInputProgram

end OAI
