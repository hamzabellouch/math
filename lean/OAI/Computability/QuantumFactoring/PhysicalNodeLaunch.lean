import Mathlib
import OAI.Computability.QuantumFactoring.NodeSplitMachine
import OAI.Computability.QuantumFactoring.MachineInitialization

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalNode

/-- The node's initial pending stack contains only the runtime modulus, enlarged
by one bit. Emission and error registers are zero. No factor data is supplied. -/
def startNet (n : ℕ) : BooleanNetwork n (configWidth n (2*n)) :=
  ((stackPush (resizeWord n (n+1))
      (Completion.zeros n ((2*n+1)*(n+1)))).pair
    (Completion.zeros n ((2*n+1)*(n+1)))).pair (constant false)

lemma startNet_eval (n : ℕ) (a : Basis n) :
    (startNet n).eval a=NodeStateCircuit.pack [natBasis (n+1) (bitsValue a).toNat] [] false := by
  have hr : (resizeWord n (n+1)).eval a=natBasis (n+1) (bitsValue a).toNat := by
    apply (bitsEquiv (n+1)).injective
    apply BitVec.eq_of_toNat_eq
    change (bitsValue ((resizeWord n (n+1)).eval a)).toNat=
      (bitsValue (natBasis (n+1) (bitsValue a).toNat)).toNat
    rw [resizeWord_value,BitVec.toNat_setWidth,natBasis_value]
  have hz : (Completion.zeros n ((2*n+1)*(n+1))).eval a=stackEncoding (2*n+1) (n+1) [] := by
    rw [Completion.zeros_eval]
    rfl
  rw [startNet,eval_pair,eval_pair,stackPush_encoding _ _ _ [] hz,hr,hz]
  apply congrArg (Fin.append _)
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  exact eval_constant false a 0

abbrev runWidth (n : ℕ) := (machine n (2*n)).width (2*n)
def runInitial (n : ℕ) : BooleanNetwork n (runWidth n) :=
  (startNet n).comp ((machine n (2*n)).initialNet (2*n))

lemma runInitial_eval (n : ℕ) (a : Basis n) :
    (runInitial n).eval a=(machine n (2*n)).initial (2*n)
      (NodeStateCircuit.pack [natBasis (n+1) (bitsValue a).toNat] [] false) := by
  rw [runInitial,eval_comp,SplitMachine.initialNet_eval,startNet_eval]

/-- Coherent launch of a complete node computation, including all literal fresh
split trials and the deterministic bounded-stack controller. Earlier entangled
histories are retained; this is not a truth-table preparation. -/
theorem launch {n p r : ℕ} {α : Type*} [Fintype α] (e : α→Basis p) (ψ : α→ℂ)
    (query : BooleanNetwork p n) (hc : (query.comp (runInitial n)).net.count≤r) :
    (programMatrix (preparedOracle (query.comp (runInitial n)) hc
      ((machine n (2*n)).program (2*n)))).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
    encodeState (fun ar : α×SplitMachine.Trace n (2*n)=>packed r (e ar.1)
      ((machine n (2*n)).encoded ((startNet n).eval (query.eval (e ar.1))) (2*n) ar.2))
      (RecordedHistory.appendState ψ (fun a=>(machine n (2*n)).state
        ((startNet n).eval (query.eval (e a))) (2*n))) := by
  apply preparedOracle_encode_dependent e
    (fun a=>(machine n (2*n)).encoded ((startNet n).eval (query.eval (e a))) (2*n)) ψ
    (fun a=>(machine n (2*n)).state ((startNet n).eval (query.eval (e a))) (2*n))
    (query.comp (runInitial n)) hc ((machine n (2*n)).program (2*n))
  intro a
  rw [eval_comp,runInitial,eval_comp,SplitMachine.initialNet_eval,SplitMachine.program_state]

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
