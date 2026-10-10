import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeMachine

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Literal clean initialization: retain the runtime controller word and create
only zero history/output/scratch fields. No query result is precomputed. -/
def initialNet : (t : ℕ) → BooleanNetwork c (M.width t)
  | 0 => select id
  | t+1 => packNet M.updateWork
      (packNet M.initWork (initialNet t) (Completion.zeros c (NodeKernel.width n)))
      (Completion.zeros c c)

lemma initialNet_eval (t : ℕ) (x : Basis c) :
    (M.initialNet t).eval x=M.initial t x := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    rw [initialNet,packNet_eval,packNet_eval,Completion.zeros_eval,Completion.zeros_eval,ih]
    rfl

lemma initialNet_count (t : ℕ) : (M.initialNet t).net.count=
    t*(NodeKernel.width n+M.initWork+c+M.updateWork) := by
  induction t with
  | zero=>simp [initialNet, count_select]
  | succ t ih=>
    simp only [initialNet,packNet_count,Completion.zeros_count,ih]
    ring

/-- A whole fixed-period machine can itself be launched coherently from a
Boolean-computed runtime controller state, retaining earlier history exactly. -/
theorem launch_on_history {α : Type*} [Fintype α] {p r : ℕ}
    (e : α→Basis p) (ψ : α→ℂ) (v : BooleanNetwork p c) (t : ℕ)
    (hc : (v.comp (M.initialNet t)).net.count ≤ r) :
    (programMatrix (preparedOracle (v.comp (M.initialNet t)) hc (M.program t))).mulVec
      (encodeState (fun a=>packed r (e a) (fun _=>false)) ψ)=
      encodeState (fun ar : α×Trace n t => packed r (e ar.1)
        (M.encoded (v.eval (e ar.1)) t ar.2))
        (RecordedHistory.appendState ψ (fun a=>M.state (v.eval (e a)) t)) := by
  apply preparedOracle_encode_dependent e (fun a=>M.encoded (v.eval (e a)) t) ψ
    (fun a=>M.state (v.eval (e a)) t) (v.comp (M.initialNet t)) hc (M.program t)
  intro a
  rw [eval_comp,M.initialNet_eval,M.program_state]

end NodeMachine
end ExactQuantumFactoring


end

end OAI
