import OAI.Computability.PerfectCompleteness.Foundations.PCPSourceHardness
import OAI.Computability.PerfectCompleteness.Machines.SourceOccurrenceMachine

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceProducer

open Turing UniqueGamesTheorem.Foundations Complexity

noncomputable section

def normalizedComputation :
    TM2ComputableInPolyTime formulaBits SourceOccurrenceEncoding.bits
      PCPSource.normalizedFormula := by
  change TM2ComputableInPolyTime formulaBits SourceOccurrenceEncoding.bits
    (fun formula => id (PCPSource.normalizedFormula formula))
  exact MachineSequential.composeBits (f := PCPSource.normalizedFormula) (g := id)
    PCPSourceMachine.normalizedComputation
    SourceOccurrenceMachine.computableInPolyTime

theorem normalized_finiteAlphabet :
    MachineFiniteAlphabet.FiniteAlphabet normalizedComputation.tm :=
  MachineFiniteAlphabet.composeBits PCPSourceMachine.normalizedComputation
    SourceOccurrenceMachine.computableInPolyTime PCPSourceMachine.normalized_finiteAlphabet
    SourceOccurrenceMachine.computation_finiteAlphabet

def rawComputation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) SourceOccurrenceEncoding.bits
      PCPSourceMachine.rawSource := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) SourceOccurrenceEncoding.bits
    (fun input => id (PCPSourceMachine.rawSource input))
  exact MachineSequential.composeBits (f := PCPSourceMachine.rawSource) (g := id)
    PCPSourceMachine.rawComputation
    SourceOccurrenceMachine.computableInPolyTime

theorem raw_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet rawComputation.tm :=
  MachineFiniteAlphabet.composeBits PCPSourceMachine.rawComputation
    SourceOccurrenceMachine.computableInPolyTime PCPSourceMachine.raw_finiteAlphabet
    SourceOccurrenceMachine.computation_finiteAlphabet

def computation {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) SourceOccurrenceEncoding.bits
      (PCPSourceHardness.formula source) := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) SourceOccurrenceEncoding.bits
    (fun input => id (PCPSourceHardness.formula source input))
  exact MachineSequential.composeBits (f := PCPSourceHardness.formula source) (g := id)
    (PCPSourceHardness.computation source)
    SourceOccurrenceMachine.computableInPolyTime

theorem computation_finiteAlphabet {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language)
    (finiteSource : MachineFiniteAlphabet.FiniteAlphabet source.computation.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computation source).tm :=
  MachineFiniteAlphabet.composeBits (PCPSourceHardness.computation source)
    SourceOccurrenceMachine.computableInPolyTime
    (PCPSourceHardness.computation_finiteAlphabet source finiteSource)
    SourceOccurrenceMachine.computation_finiteAlphabet

end
end PerfectCompleteness.SourceOccurrenceProducer


namespace PerfectCompleteness.NormalizedSourceInput


open Turing UniqueGamesTheorem.Foundations Complexity Target

structure Input where
  formula : Formula
  nonempty : formula.clauses ≠ []
  distinct : ∀ clause ∈ formula.clauses, ∀ i j : Fin 3,
    clause[i].variableIndex = clause[j].variableIndex → i = j

def bits (input : Input) : List Bool := SourceOccurrenceEncoding.bits input.formula

def variableCount (input : Input) : Nat := input.formula.variables
def clauseCount (input : Input) : Nat := input.formula.clauses.length

theorem clauseCount_positive (input : Input) : 0 < clauseCount input :=
  List.length_pos_iff.mpr input.nonempty

instance clauseCount_neZero (input : Input) : NeZero (clauseCount input) :=
  ⟨Nat.ne_of_gt (clauseCount_positive input)⟩

def clauses (input : Input) : Fin (clauseCount input) → SourceClause.NormalizedClause (variableCount input) :=
  fun index =>
    { clause := input.formula.clauses[index.val]
      distinct := input.distinct _ (List.getElem_mem index.isLt) }

@[simp] theorem clause_eq (input : Input) (index : Fin (clauseCount input)) :
    (clauses input index).clause = input.formula.clauses[index.val] := rfl

@[simp] theorem variable_eq (input : Input) (index : Fin (clauseCount input)) (slot : Fin 3) :
    (clauses input index).variable slot = input.formula.clauses[index.val][slot].variableIndex := rfl

@[simp] theorem signs_eq (input : Input) (index : Fin (clauseCount input)) :
    (clauses input index).signs =
      (input.formula.clauses[index.val][0].positive,
       input.formula.clauses[index.val][1].positive,
       input.formula.clauses[index.val][2].positive) := rfl

theorem bits_eq (input : Input) :
    bits input = encodeWord (variableCount input) ++ encodeWord (clauseCount input) ++
      SourceOccurrenceEncoding.body 0 input.formula.clauses :=
  SourceOccurrenceEncoding.bits_eq input.formula

theorem decode_bits (input : Input) :
    SourceOccurrenceEncoding.decode (bits input) = some input.formula :=
  SourceOccurrenceEncoding.decode_bits input.formula

theorem ext (first second : Input) (same : first.formula = second.formula) : first = second := by
  cases first
  cases second
  cases same
  rfl

theorem bits_injective : Function.Injective bits := by
  intro first second same
  exact ext first second (SourceOccurrenceEncoding.bits_injective same)

noncomputable section

def normalized (formula : Formula) : Input where
  formula := PCPSource.normalizedFormula formula
  nonempty := PCPSource.normalizedFormula_nonempty formula
  distinct := PCPSource.normalizedFormula_distinct formula

@[simp] theorem normalized_formula (formula : Formula) :
    (normalized formula).formula = PCPSource.normalizedFormula formula := rfl

@[simp] theorem normalized_bits (formula : Formula) :
    bits (normalized formula) = SourceOccurrenceEncoding.bits (PCPSource.normalizedFormula formula) := rfl

theorem violatedCount_eq_failedCount (input : Input)
    (assignment : Fin input.formula.variables → Bool) :
    SourceGame.violatedCount (clauses input) assignment =
      PCP.NameCompaction.failedCount input.formula assignment := by
  rw [PCPSource.failedCount_eq_fin_sum]
  rfl

theorem clauseGap_of_count (input : Input) (denominator : Nat)
    (positive : 0 < denominator)
    (countGap : ∀ assignment : Fin input.formula.variables → Bool,
      input.formula.clauses.length ≤
        denominator * PCP.NameCompaction.failedCount input.formula assignment) :
    SourceAmplification.ClauseGap (clauses input) (1 / (denominator : ℚ)) := by
  intro assignment
  have hnat := countGap assignment
  have hq : (input.formula.clauses.length : ℚ) ≤
      (denominator : ℚ) * (PCP.NameCompaction.failedCount input.formula assignment : ℚ) := by
    exact_mod_cast hnat
  change (1 / (denominator : ℚ)) * (input.formula.clauses.length : ℚ) ≤ _
  erw [violatedCount_eq_failedCount]
  rw [one_div_mul_eq_div]
  have hden : (0 : ℚ) < denominator := by exact_mod_cast positive
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hq)

theorem clauseGap_mk (formula : Formula) (nonempty : formula.clauses ≠ [])
    (distinct : ∀ clause ∈ formula.clauses, ∀ i j : Fin 3,
      clause[i].variableIndex = clause[j].variableIndex → i = j)
    (denominator : Nat) (positive : 0 < denominator)
    (countGap : ∀ assignment : Fin formula.variables → Bool,
      formula.clauses.length ≤ denominator * PCP.NameCompaction.failedCount formula assignment) :
    SourceAmplification.ClauseGap (clauses ⟨formula, nonempty, distinct⟩)
      (1 / (denominator : ℚ)) :=
  clauseGap_of_count ⟨formula, nonempty, distinct⟩ denominator positive countGap

theorem normalized_clauseGap (formula : Formula) (unsatisfiable : ¬formula.Satisfiable) :
    SourceAmplification.ClauseGap (clauses (normalized formula)) PCPSource.sourceGap :=
  clauseGap_mk (PCPSource.normalizedFormula formula)
    (PCPSource.normalizedFormula_nonempty formula) (PCPSource.normalizedFormula_distinct formula)
    PCPSource.sourceDenominator PCPSource.sourceDenominator_pos
    (PCPSource.normalizedFormula_count_gap formula unsatisfiable)

def normalizedComputation : TM2ComputableInPolyTime formulaBits bits normalized where
  toTM2ComputableAux := SourceOccurrenceProducer.normalizedComputation.toTM2ComputableAux
  time := SourceOccurrenceProducer.normalizedComputation.time
  outputsFun formula := SourceOccurrenceProducer.normalizedComputation.outputsFun formula

theorem normalized_finiteAlphabet :
    MachineFiniteAlphabet.FiniteAlphabet normalizedComputation.tm :=
  SourceOccurrenceProducer.normalized_finiteAlphabet

def raw (input : List Bool) : Input := normalized (BinaryLanguage.totalRename input)

@[simp] theorem raw_formula (input : List Bool) :
    (raw input).formula = PCPSourceMachine.rawSource input := rfl

def rawComputation : TM2ComputableInPolyTime (id : List Bool → List Bool) bits raw where
  toTM2ComputableAux := SourceOccurrenceProducer.rawComputation.toTM2ComputableAux
  time := SourceOccurrenceProducer.rawComputation.time
  outputsFun input := SourceOccurrenceProducer.rawComputation.outputsFun input

theorem raw_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet rawComputation.tm :=
  SourceOccurrenceProducer.raw_finiteAlphabet

theorem raw_satisfiable_iff (input : List Bool) :
    (raw input).formula.Satisfiable ↔ BinaryLanguage.language input :=
  PCPSourceMachine.rawSource_satisfiable_iff input

theorem raw_clauseGap (input : List Bool) (rejected : ¬BinaryLanguage.language input) :
    SourceAmplification.ClauseGap (clauses (raw input)) PCPSource.sourceGap :=
  normalized_clauseGap (BinaryLanguage.totalRename input)
    (fun satisfiable => rejected ((BinaryLanguage.totalRename_satisfiable_iff input).mp satisfiable))

def fromReduction {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) (input : List Bool) : Input :=
  normalized (source.reduce input)

@[simp] theorem fromReduction_formula {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) (input : List Bool) :
    (fromReduction source input).formula = PCPSourceHardness.formula source input := rfl

def computation {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) bits (fromReduction source) where
  toTM2ComputableAux := (SourceOccurrenceProducer.computation source).toTM2ComputableAux
  time := (SourceOccurrenceProducer.computation source).time
  outputsFun input := (SourceOccurrenceProducer.computation source).outputsFun input

theorem computation_finiteAlphabet {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language)
    (finiteSource : MachineFiniteAlphabet.FiniteAlphabet source.computation.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computation source).tm :=
  SourceOccurrenceProducer.computation_finiteAlphabet source finiteSource

theorem producer (language : List Bool → Prop) (membership : CookLevin.InNP language) :
    ∃ source : CookLevin.PolynomialThreeSATReduction language,
    ∃ runtime : TM2ComputableInPolyTime (id : List Bool → List Bool) bits (fromReduction source),
      MachineFiniteAlphabet.FiniteAlphabet runtime.tm ∧
      ∀ input : List Bool,
        ((fromReduction source input).formula.Satisfiable ↔ language input) ∧
        (¬language input → SourceAmplification.ClauseGap
          (clauses (fromReduction source input)) PCPSource.sourceGap) := by
  obtain ⟨source, finiteSource⟩ := CookLevin.Completeness.threeSATReduction language membership
  refine ⟨source, computation source, computation_finiteAlphabet source finiteSource, ?_⟩
  intro input
  constructor
  · exact (PCPSource.normalizedFormula_satisfiable_iff (source.reduce input)).trans
      (source.correct input).symm
  · intro rejected
    exact normalized_clauseGap (source.reduce input)
      (fun sat => rejected ((source.correct input).mpr sat))

end
end PerfectCompleteness.NormalizedSourceInput

end OAI
