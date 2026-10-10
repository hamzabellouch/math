import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeMachine
import OAI.Computability.QuantumFactoring.PhysicalTreeMass

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

/-- Access only retained earlier wires. No history is recomputed. -/
def previousNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (M.width t) :=
  (select (firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork)).comp
    (select (firstRegister (M.width t) (NodeKernel.width n) M.initWork))
def lastNodeNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (NodeKernel.width n) :=
  (select (firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork)).comp
    (select (targetRegister (M.width t) (NodeKernel.width n) M.initWork))

lemma previousNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.previousNet t).eval (M.encoded x (t+1) (h,r))=M.encoded x t h := by
  rw [previousNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (NodeKernel.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) ∘
      firstRegister (M.width t) (NodeKernel.width n) M.initWork=_
  rw [packed_first,packed_first]
lemma lastNodeNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : NodeKernel.Raw n) :
    (M.lastNodeNet t).eval (M.encoded x (t+1) (h,r))=
      NodeKernel.encoding (M.query.eval (M.config x t h)) r := by
  rw [lastNodeNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (NodeKernel.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork) ∘
      targetRegister (M.width t) (NodeKernel.width n) M.initWork=_
  rw [packed_first,packed_targetRegister]

def firstNodeNet : (t : ℕ)→BooleanNetwork (M.width (t+1)) (NodeKernel.width n)
  | 0=>M.lastNodeNet 0
  | t+1=>(M.previousNet (t+1)).comp (firstNodeNet t)
def firstRaw : (t : ℕ)→Trace n (t+1)→NodeKernel.Raw n
  | 0,h=>h.2
  | t+1,h=>firstRaw t h.1
lemma firstNodeNet_encoded (x : Basis c) (t : ℕ) (h : Trace n (t+1)) :
    (M.firstNodeNet t).eval (M.encoded x (t+1) h)=NodeKernel.encoding (M.query.eval x) (firstRaw t h) := by
  induction t with
  | zero=>exact M.lastNodeNet_encoded x 0 h.1 h.2
  | succ t ih=>
    rw [firstNodeNet,eval_comp,M.previousNet_encoded,ih]
    rfl
lemma first_passed (x : Basis c) (t : ℕ) (h : Trace n (t+1))
    (hp : M.passed x (t+1) h) : NodeKernel.passed (M.query.eval x) (firstRaw t h) := by
  induction t with
  | zero=>exact hp.2
  | succ t ih=>exact ih h.1 hp.1
lemma firstNodeNet_count (t : ℕ) : (M.firstNodeNet t).net.count=0 := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [firstNodeNet,count_comp,previousNet,count_comp,count_select,ih,add_zero]

end NodeMachine
end ExactQuantumFactoring


end

end OAI
