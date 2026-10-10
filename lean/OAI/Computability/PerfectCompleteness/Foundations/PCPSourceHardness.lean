import OAI.Computability.PerfectCompleteness.Machines.Completeness
import OAI.Computability.PerfectCompleteness.Machines.PreprocessingMachineLemmas

namespace OAI

section

namespace PerfectCompleteness.PCPSourceHardness

open Turing UniqueGamesTheorem.Foundations Complexity Target

noncomputable section

def formula {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) (input : List Bool) : Formula :=
  PCPSource.normalizedFormula (source.reduce input)

def computation {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits (formula source) := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => PCPSource.normalizedFormula (source.reduce input))
  exact MachineSequential.composeBits source.computation PCPSourceMachine.normalizedComputation

theorem computation_finiteAlphabet {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language)
    (finiteSource : MachineFiniteAlphabet.FiniteAlphabet source.computation.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computation source).tm :=
  MachineFiniteAlphabet.composeBits source.computation PCPSourceMachine.normalizedComputation
    finiteSource PCPSourceMachine.normalized_finiteAlphabet

theorem normalizedSource (language : List Bool → Prop) (membership : CookLevin.InNP language) :
    ∃ source : CookLevin.PolynomialThreeSATReduction language,
    ∃ runtime : TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits (formula source),
      MachineFiniteAlphabet.FiniteAlphabet runtime.tm ∧
      ∀ input : List Bool,
        ((formula source input).Satisfiable ↔ language input) ∧
        (formula source input).clauses ≠ [] ∧
        (∀ (clause : Clause (formula source input).variables),
          clause ∈ (formula source input).clauses →
          ∀ i j : Fin 3, clause[i].variableIndex = clause[j].variableIndex → i = j) ∧
        (¬language input →
          SourceAmplification.ClauseGap (PCPSource.clauseFamily (source.reduce input))
            PCPSource.sourceGap) := by
  obtain ⟨source, finiteSource⟩ := CookLevin.Completeness.threeSATReduction language membership
  refine ⟨source, computation source, computation_finiteAlphabet source finiteSource, ?_⟩
  intro input
  refine ⟨?_, PCPSource.normalizedFormula_nonempty (source.reduce input), ?_, ?_⟩
  · exact (PCPSource.normalizedFormula_satisfiable_iff (source.reduce input)).trans
      (source.correct input).symm
  · intro clause mem i j same
    exact PCPSource.normalizedFormula_distinct (source.reduce input) clause mem i j same
  · intro rejected
    exact PCPSource.clauseGap (source.reduce input)
      (fun sat => rejected ((source.correct input).mpr sat))

end
end PerfectCompleteness.PCPSourceHardness

end

end OAI
