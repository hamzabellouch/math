import OAI.Computability.PerfectCompleteness.Machines.NormalizedTargetMachine

namespace OAI

section

namespace PerfectCompleteness.NormalizedTargetProducer

open Turing UniqueGamesTheorem.Foundations Complexity

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
    (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ

def construct {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) (input : List Bool) : Instance q :=
  NormalizedTarget.construct (t := t) rows repeats hn hbranch hrows δ
    (NormalizedSourceInput.fromReduction source input)

def computation {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) Encoding.gameBits
      (construct (t := t) rows repeats hn hbranch hrows δ source) := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) Encoding.gameBits
    (fun input => NormalizedTarget.construct (t := t) rows repeats hn hbranch hrows δ
      (NormalizedSourceInput.fromReduction source input))
  exact MachineSequential.composeBits
    (f := NormalizedSourceInput.fromReduction source)
    (g := NormalizedTarget.construct (t := t) rows repeats hn hbranch hrows δ)
    (NormalizedSourceInput.computation source)
    (NormalizedTargetMachine.targetComputation (t := t) rows repeats hn hbranch hrows δ)

theorem finiteAlphabet {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language)
    (finiteSource : MachineFiniteAlphabet.FiniteAlphabet source.computation.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computation (t := t) rows repeats hn hbranch hrows δ source).tm :=
  MachineFiniteAlphabet.composeBits
    (NormalizedSourceInput.computation source)
    (NormalizedTargetMachine.targetComputation (t := t) rows repeats hn hbranch hrows δ)
    (NormalizedSourceInput.computation_finiteAlphabet source finiteSource)
    (NormalizedTargetMachine.finiteAlphabet (t := t) rows repeats hn hbranch hrows δ)

theorem source_satisfiable_iff {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) (input : List Bool) :
    (NormalizedSourceInput.fromReduction source input).formula.Satisfiable ↔ language input := by
  change (PCPSource.normalizedFormula (source.reduce input)).Satisfiable ↔ language input
  exact (PCPSource.normalizedFormula_satisfiable_iff (source.reduce input)).trans
    (source.correct input).symm

theorem perfectlyComplete {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) (input : List Bool)
    (accepted : language input) :
    PerfectlyComplete (construct (t := t) rows repeats hn hbranch hrows δ source input) := by
  apply NormalizedTarget.perfectlyComplete (t := t) rows repeats hn hbranch hrows δ
    (NormalizedSourceInput.fromReduction source input)
  exact (source_satisfiable_iff source input).mpr accepted

theorem source_clauseGap {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) (input : List Bool)
    (rejected : ¬language input) :
    SourceAmplification.ClauseGap
      (NormalizedSourceInput.clauses (NormalizedSourceInput.fromReduction source input))
      PCPSource.sourceGap :=
  NormalizedSourceInput.normalized_clauseGap (source.reduce input)
    (fun satisfiable => rejected ((source.correct input).mpr satisfiable))

theorem producer (language : List Bool → Prop) (membership : CookLevin.InNP language) :
    ∃ source : CookLevin.PolynomialThreeSATReduction language,
    ∃ runtime : TM2ComputableInPolyTime (id : List Bool → List Bool) Encoding.gameBits
      (construct (t := t) rows repeats hn hbranch hrows δ source),
      MachineFiniteAlphabet.FiniteAlphabet runtime.tm ∧
      ∀ input : List Bool,
        ((NormalizedSourceInput.fromReduction source input).formula.Satisfiable ↔ language input) ∧
        (language input → PerfectlyComplete
          (construct (t := t) rows repeats hn hbranch hrows δ source input)) ∧
        (¬language input → SourceAmplification.ClauseGap
          (NormalizedSourceInput.clauses (NormalizedSourceInput.fromReduction source input))
          PCPSource.sourceGap) := by
  obtain ⟨source, finiteSource⟩ := CookLevin.Completeness.threeSATReduction language membership
  refine ⟨source, computation (t := t) rows repeats hn hbranch hrows δ source,
    finiteAlphabet (t := t) rows repeats hn hbranch hrows δ source finiteSource, ?_⟩
  intro input
  exact ⟨source_satisfiable_iff source input,
    perfectlyComplete (t := t) rows repeats hn hbranch hrows δ source input,
    source_clauseGap source input⟩

end
end PerfectCompleteness.NormalizedTargetProducer

end

end OAI
