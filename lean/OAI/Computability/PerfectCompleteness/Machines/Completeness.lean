import OAI.Computability.PerfectCompleteness.Machines.CircuitProducerStagesLemmas
import OAI.Computability.PerfectCompleteness.Machines.ProducerTimeLemmas
import OAI.Computability.UniqueGames.Machines.GraphCounterStartLemmas
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.Completeness

open Turing

theorem circuitProducerFinite :
    MachineFiniteAlphabet.FiniteAlphabet CircuitProducer.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

def verifierReduction (V : NPVerifier) : PolynomialThreeSATReduction V.Accepts where
  reduce input := (VerifierCircuit.circuitOfVerifier V input).toFormula
  computation := MachineSequential.composeBits (ProducerMachine.computableInPolyTime V)
    CircuitProducer.computableInPolyTime
  correct input := (VerifierCircuit.circuitOfVerifier_correct V input).symm

theorem verifierReduction_finiteAlphabet (V : NPVerifier) :
    MachineFiniteAlphabet.FiniteAlphabet (verifierReduction V).computation.tm :=
  MachineFiniteAlphabet.composeBits (ProducerMachine.computableInPolyTime V)
    CircuitProducer.computableInPolyTime (ProducerMachine.finiteAlphabet V) circuitProducerFinite

theorem threeSATReduction (language : List Bool → Prop) (membership : InNP language) :
    ∃ source : PolynomialThreeSATReduction language,
      MachineFiniteAlphabet.FiniteAlphabet source.computation.tm := by
  obtain ⟨V, recognized⟩ := membership
  let source : PolynomialThreeSATReduction language := {
    reduce := (verifierReduction V).reduce
    computation := (verifierReduction V).computation
    correct := fun input => (recognized input).trans ((verifierReduction V).correct input) }
  exact ⟨source, verifierReduction_finiteAlphabet V⟩

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.Completeness

end

end

end OAI
