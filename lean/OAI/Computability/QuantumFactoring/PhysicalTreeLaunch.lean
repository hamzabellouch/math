import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeCompletion
import OAI.Computability.QuantumFactoring.TreeInitialization
import OAI.Computability.QuantumFactoring.TreeHistoryAccess

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

def startNet (n : ℕ) : BooleanNetwork n (configWidth n) :=
  stackPush (select id) (Completion.zeros n (configWidth n))
lemma startNet_eval (n : ℕ) (a : Basis n) :
    (startNet n).eval a=stackEncoding (capacity n) n [a] := by
  rw [startNet,stackPush_encoding _ _ _ [] (by rw [Completion.zeros_eval];rfl)]
  rfl
lemma startNet_nat {n N : ℕ} : (startNet n).eval (natBasis n N)=initialQueue n N := by
  rw [startNet_eval]
  rfl
abbrev steps (n : ℕ) := 2*n^2
abbrev width (n : ℕ) := (machine n).width (steps n)
def initialNet (n : ℕ) : BooleanNetwork n (width n) :=
  (startNet n).comp ((machine n).initialNet (steps n))
lemma initialNet_eval {n N : ℕ} : (initialNet n).eval (natBasis n N)=
    (machine n).initial (steps n) (initialQueue n N) := by
  rw [initialNet,eval_comp,NodeMachine.initialNet_eval,startNet_nat]

/-- Literal runtime-input initialization and physical chronological tree
construction, coherently over all input words. No factors initialize the input. -/
theorem launch {n p r : ℕ} {α : Type*} [Fintype α] (e : α→Basis p) (ψ : α→ℂ)
    (input : BooleanNetwork p n) (hc : (input.comp (initialNet n)).net.count ≤ r) :
    (programMatrix (preparedOracle (input.comp (initialNet n)) hc
      ((machine n).program (steps n)))).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun ar : α×NodeMachine.Trace n (steps n)=>packed r (e ar.1)
      ((machine n).encoded ((startNet n).eval (input.eval (e ar.1))) (steps n) ar.2))
      (RecordedHistory.appendState ψ (fun a=>(machine n).state
        ((startNet n).eval (input.eval (e a))) (steps n))) := by
  apply preparedOracle_encode_dependent e
    (fun a=>(machine n).encoded ((startNet n).eval (input.eval (e a))) (steps n)) ψ
    (fun a=>(machine n).state ((startNet n).eval (input.eval (e a))) (steps n))
    (input.comp (initialNet n)) hc ((machine n).program (steps n))
  intro a
  rw [eval_comp,initialNet,eval_comp,NodeMachine.initialNet_eval,NodeMachine.program_state]

/-- Actual root readout from earlier retained wires, not a factor-table lookup. -/
def rootResult (n t : ℕ) : BooleanNetwork ((machine n).width (t+1)) (tensorWidth n n) :=
  ((machine n).firstNodeNet t).comp (nodeResult n)

lemma query_initial (n N : ℕ) : (query n).eval (initialQueue n N)=natBasis n N :=
  query_encoding n (natBasis n N) []

/-- Every flagged chronological raw history has the literal sorted and padded
root encoding in the fixed root-output network. No other run supplies it. -/
theorem root_correct {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n (t+1))
    (hp : (machine n).passed (initialQueue n N) (t+1) h) :
    ∃ zs : List (Basis n), zs.length=n ∧ CorrectEncoding N n (SortedWords.numbers zs) ∧
      (rootResult n t).eval ((machine n).encoded (initialQueue n N) (t+1) h)=
        SortedWords.layout n n zs := by
  have hp0 := (machine n).first_passed (initialQueue n N) t h hp
  change NodeKernel.passed ((query n).eval (initialQueue n N)) (NodeMachine.firstRaw t h) at hp0
  rw [query_initial] at hp0
  have hv : (bitsValue (natBasis n N)).toNat=N := by rw [natBasis_value,Nat.mod_eq_of_lt hb]
  have hp' : (PhysicalNode.machine n (2*n)).passed
      (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) (NodeMachine.firstRaw t h) := by
    simpa only [NodeKernel.passed,NodeKernel.start,PhysicalNode.startNet_eval,hv] using hp0
  obtain ⟨zs,hl,hc,he⟩ := PhysicalNode.complete_output hn hN hb (NodeMachine.firstRaw t h) hp'
  refine ⟨zs,hl,hc,?_⟩
  rw [rootResult,eval_comp,NodeMachine.firstNodeNet_encoded]
  change (nodeResult n).eval (NodeKernel.encoding ((query n).eval (initialQueue n N))
    (NodeMachine.firstRaw t h))=_
  rw [query_initial,nodeResult,eval_comp,NodeKernel.encoding,SplitMachine.current_encoded,
    NodeKernel.start,PhysicalNode.startNet_eval,hv]
  exact he

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
